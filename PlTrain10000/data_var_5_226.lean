variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217558055658675769836978725129 : ((((p3 ∧ p1) ∨ True) → False) → (p2 ∨ (p3 ∨ (p3 ∧ (((False ∧ p3) ∧ (((False ∨ p1) ∨ p2) ∧ False)) ∧ ((False ∨ p1) ∨ (True ∨ p2))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p3 ∧ p1) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40984975514303253021697573376 : ((((p3 ∧ ((((p3 → p4) ∨ ((False ∧ p2) ∨ p4)) → (False ∧ (((False → (True ∨ p5)) → p1) → p5))) ∧ True)) ∨ (True → p2)) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187768801428966382107101962413 : ((p2 → (p2 ∨ (p2 → (p1 ∧ (p3 ∨ ((True ∨ p1) → p5)))))) → ((p1 → (p2 → p5)) ∨ ((((p3 ∧ p2) ∧ (p4 ∧ p5)) ∧ p5) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262121514338936600093970802067 : (True ∧ (((((p1 ∨ p5) ∨ True) → (((True ∧ (((p5 → p2) ∧ p2) ∧ p1)) → (((p1 → (False → True)) ∨ p3) ∧ p5)) ∨ p5)) ∧ True) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111804444439764645714040001296 : ((((((p2 → (True ∧ ((((p4 ∧ p1) ∧ p1) ∧ p2) ∧ (p3 → (p3 ∧ p2))))) ∨ p2) ∨ (p5 ∧ p1)) → (p3 ∨ p3)) ∨ True) ∨ (True → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356767519540233638464535882785 : (p5 → ((((p5 ∨ p5) ∨ False) → (p4 ∨ True)) → ((((((((False → p5) → False) → False) ∨ ((p3 ∨ p1) ∨ True)) → False) ∨ p4) ∧ p4) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58325504813166152966824198863 : (((False ∨ False) ∧ (p1 ∨ (p1 → ((((p3 ∨ (p5 ∧ p4)) ∨ (p1 ∨ ((p4 → p2) ∨ p3))) → ((p4 ∧ p3) → p5)) → (p3 ∧ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_243997208949524593429307374913 : ((True ∧ p1) ∨ (p3 → (((((p4 ∨ (p1 → True)) → (p3 → (p1 ∨ p2))) ∨ p5) ∨ ((p5 ∨ p4) ∨ p3)) ∧ (((p4 ∧ p1) → True) ∧ True)))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342077817148152781603153623042 : (p2 → ((p4 ∧ (p1 ∧ (((p5 → (p3 → p4)) → ((p5 → ((p1 ∧ (p5 ∨ (p1 → p2))) → True)) ∧ False)) ∧ p4))) → (p3 ∧ (False ∧ False)))) := by
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
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h9 : (p5 → (p3 → p4)) := by
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h12 := h7 h9
  -- We need to get the right conjuct of h12 based on <expert-advice>.
  let h13 := h12.right
  -- False on the left can always be used.
  apply False.elim h13
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h14 := h2.left
  let h15 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h16 := h15.left
  let h17 := h15.right
  -- Conjunctions on the left can always be decomposed.
  let h18 := h17.left
  let h19 := h17.right
  -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
  have h20 : (p5 → (p3 → p4)) := by
    -- Implications on the right can always be decomposed.
    intro h21
    -- Implications on the right can always be decomposed.
    intro h22
    -- One of the premise coincides with the conclusion.
    exact h19
  -- We have shown the premise of h18, we can now drive its conclusion.
  let h23 := h18 h20
  -- We need to get the right conjuct of h23 based on <expert-advice>.
  let h24 := h23.right
  -- False on the left can always be used.
  apply False.elim h24
  -- Conjunctions on the left can always be decomposed.
  let h25 := h2.left
  let h26 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h27 := h26.left
  let h28 := h26.right
  -- Conjunctions on the left can always be decomposed.
  let h29 := h28.left
  let h30 := h28.right
  -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
  have h31 : (p5 → (p3 → p4)) := by
    -- Implications on the right can always be decomposed.
    intro h32
    -- Implications on the right can always be decomposed.
    intro h33
    -- One of the premise coincides with the conclusion.
    exact h30
  -- We have shown the premise of h29, we can now drive its conclusion.
  let h34 := h29 h31
  -- We need to get the right conjuct of h34 based on <expert-advice>.
  let h35 := h34.right
  -- False on the left can always be used.
  apply False.elim h35



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185310312863934940955689880170 : ((p3 ∧ ((((p2 → p1) ∨ p3) ∨ ((p3 ∨ False) ∧ p3)) ∨ p5)) ∨ ((True → p5) ∨ ((p3 ∨ (((p3 ∨ p3) ∧ (p5 ∧ p5)) → p5)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66556103006777126597684198187 : ((True → ((((p5 ∨ p1) ∧ p1) ∧ ((p1 ∧ p2) ∨ (p3 → (((p4 ∨ (True ∧ ((p2 → p5) ∧ False))) ∨ p5) ∧ p2)))) ∧ (p3 ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178014883383222114383045665970 : (((True → ((p2 ∧ p3) ∧ (p4 → ((p2 → (p5 → p5)) → True)))) ∨ p2) ∨ (True → (p1 ∨ ((p2 ∨ (p2 → (p5 → (p4 ∧ p1)))) ∨ True)))) := by
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
theorem thm_5_vars_213324503125554884446612729381 : (((p1 ∧ (p5 ∧ p2)) ∧ True) ∨ ((((p3 ∧ (p2 ∨ (True ∨ (((((p2 ∧ True) → (p5 ∧ False)) → p1) ∨ p5) ∨ p4)))) ∨ p4) → p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190504795247633696210083239678 : ((((True ∨ ((False ∨ False) → (False ∨ p5))) ∨ p1) → p1) ∨ (False → ((False → (((True ∨ p2) ∧ (p2 ∨ ((p1 → p3) ∧ p1))) → True)) → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_865204735418847559769760999762 : (((((((p1 ∨ True) ∨ (p3 ∨ p1)) → p5) → (((((((p4 ∧ True) ∨ p2) ∨ False) → False) ∨ p2) ∨ p5) ∨ (False → (p4 ∧ p5)))) → False) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p1 ∨ True) ∨ (p3 ∨ p1)) → p5) → (((((((p4 ∧ True) ∨ p2) ∨ False) → False) ∨ p2) ∨ p5) ∨ (False → (p4 ∧ p5)))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h4
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115145594896464380510838141479 : (((p4 ∧ (p3 → ((p4 ∨ (p2 ∧ (False ∧ p1))) → (p1 ∨ p1)))) → (((((True ∨ False) → p3) → p5) → (p1 → p4)) ∧ p3)) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180926643149296241282867837902 : (((p2 ∧ p1) ∧ ((True ∧ ((True ∧ (p5 ∧ (p5 → False))) ∨ p5)) ∧ p2)) → ((((True ∨ (p3 ∨ p5)) → (p3 ∨ True)) → (p3 ∧ p4)) ∨ True)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
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
theorem thm_5_vars_123681593977184997781094838589 : (((p5 ∧ ((((True → (p4 ∧ p1)) ∨ p1) → (((True ∧ p3) ∧ False) ∨ p1)) → False)) → (((p2 ∧ p5) → p3) → (p2 ∧ p3))) → (p4 ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165170963408757744745503986562 : (((p1 ∧ ((p2 ∨ ((True → (p4 ∧ p4)) → (False ∨ (p2 ∨ p1)))) ∧ p5)) ∧ (p1 ∨ p5)) ∨ ((p3 ∨ (False → True)) ∨ (False ∧ (False ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_674745626799553072581420306830 : ((((p3 → ((((p2 ∧ (p3 → p1)) ∨ p2) ∧ (p2 → p1)) ∧ (((True → False) ∨ p3) → ((True ∨ p1) ∧ p5)))) → (p4 → (p1 ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58840271744603707178039415245 : (((True ∧ p1) ∨ ((((p3 → (p5 ∨ p5)) ∧ (p1 ∨ p2)) → (p4 → ((p5 ∧ (p2 ∧ (False → p3))) ∨ p3))) → (p3 ∧ (p2 → p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314750979690541811994075434863 : (p3 ∨ (((p3 → (True ∨ False)) → (((((False ∨ p1) ∧ p4) → p4) → True) ∧ False)) ∨ (p4 ∨ ((p4 ∧ (p5 ∧ p5)) ∨ (False → (p2 → p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180141883935670119477780010406 : ((((p3 ∨ ((False ∧ (True ∨ p5)) ∨ ((p5 → p3) → p4))) → p5) → True) → (p4 ∨ (((p5 ∧ (False ∨ False)) ∧ p3) ∨ ((p4 → p2) ∨ True)))) := by
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
theorem thm_5_vars_348509354616190230308451213265 : (p3 → (p3 ∧ ((((p4 ∨ p1) ∧ ((True ∨ p3) → p2)) → False) ∨ ((((True → (False ∨ True)) → (False ∨ (False → p3))) ∨ p1) ∨ (True ∧ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112768082530262379547476639951 : (((((p4 → (p1 ∨ (p1 → (p1 → p1)))) ∨ (p3 → p1)) → ((((p1 ∧ ((p5 ∧ False) → p4)) ∨ p2) → True) ∧ False)) → p5) ∨ (p2 → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p4 → (p1 ∨ (p1 → (p1 → p1)))) ∨ (p3 → p1)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_596249152106169230437739850292 : (((((False ∧ (True ∧ (((p1 ∨ False) ∨ p4) ∧ p3))) ∧ ((p1 → False) ∧ ((((p5 → p1) → (p5 ∧ p1)) ∧ False) → (False ∧ p4)))) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168594329084276846254501209220 : ((p2 ∧ (p4 ∨ (((True ∨ p5) ∧ ((p3 ∧ p4) ∨ (p4 ∧ p1))) → ((p4 ∧ p5) ∨ p3)))) → (((p5 ∨ False) ∨ (p3 ∨ p2)) ∨ (p4 ∧ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164808308548500291933451513032 : ((((True ∧ p3) ∧ ((((False → False) ∧ p1) ∨ (p5 ∨ p4)) ∧ ((True → p5) ∨ p5))) ∨ True) ∨ ((((p2 → p5) ∨ (p1 → p3)) ∨ p2) ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_743246147735113973385221793111 : ((((p4 → p5) ∨ ((p4 ∧ (p5 → p4)) ∧ (((p3 ∨ p1) ∨ (True ∧ ((p3 → p3) ∨ (((False ∨ p3) ∨ (p2 ∨ p4)) ∧ True)))) ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42631030303252819032390522107 : (((p3 ∨ ((p4 → p1) ∨ ((((p5 ∧ (p4 → ((p4 → True) → p3))) ∧ ((False ∧ True) ∧ False)) ∨ (p3 → (False ∧ False))) ∧ p1))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185563935635627411673208960222 : ((p4 ∨ ((True ∧ False) ∨ ((p4 ∧ (p1 ∧ p4)) ∨ (False → p1)))) ∨ (p3 ∧ (p3 ∧ (False → (p2 → ((False → p4) ∨ ((p2 ∨ p1) → p2))))))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65694046620871779307118794656 : ((p4 ∨ ((p2 ∨ (p2 ∨ ((p4 ∨ p4) ∨ ((((p1 → p4) ∧ p3) ∨ (((p3 → p5) → p5) → True)) → ((p3 ∧ True) → p4))))) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147616561700202733976361917657 : ((((p4 → ((((((p3 ∧ p4) ∧ p1) ∧ p5) ∨ p2) ∨ (p3 ∨ True)) ∨ (p5 ∨ (p1 → p3)))) ∨ p1) → p2) ∨ (p3 → ((p4 ∧ p5) → p4))) := by
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
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54747882845998173393376885347 : ((((p4 ∨ True) ∧ (True → (False → (p1 ∧ False)))) → ((((p5 ∧ p5) ∧ (p1 ∧ ((p1 ∧ True) ∧ p5))) ∨ (p5 ∧ True)) ∨ (False → p3))) ∨ p3) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173209125405928341289275161485 : ((p5 ∨ ((((p4 → p4) ∧ (p1 ∧ p5)) ∨ p5) → (p3 ∨ (p4 ∧ (p1 → p3))))) ∨ ((p4 ∨ ((p4 ∧ (p1 ∨ (p2 ∨ p4))) → p4)) ∨ p3)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659323448183579343525283904639 : ((((p5 → ((p4 ∨ p3) ∨ ((((True ∨ ((p3 ∨ (p4 ∨ (True → (p4 ∧ (p1 ∧ False))))) → True)) → False) ∨ p1) ∨ p5))) ∨ (p2 ∨ True)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_758772643991076924451515836836 : (((p2 ∧ ((p5 ∨ ((p3 ∨ ((p5 ∧ ((p1 → ((p2 ∨ (False → p2)) ∧ (p4 → (p2 → (p5 ∨ p2))))) ∨ True)) → False)) ∧ True)) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174264406382868653004500744208 : (((((p5 ∨ p2) ∨ ((False ∧ (True ∨ p4)) ∨ p2)) → p5) ∧ (p3 ∧ (p2 ∧ p4))) → (False ∨ (((p4 → False) ∨ p3) ∨ ((p4 ∨ p4) → True)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56914285488316923076075695512 : (((p5 ∧ (p1 ∨ p5)) ∧ ((((p2 ∨ (True ∧ False)) → (p3 ∧ (p3 → (False → p1)))) ∨ ((p1 ∧ p1) ∧ True)) ∨ ((p3 ∧ False) ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136062126893368609611320472291 : (((((p4 → p1) ∨ (p1 ∧ p5)) ∧ (p5 ∧ True)) ∧ (((p5 ∧ (p2 ∨ p4)) ∨ ((False → False) ∨ (p4 ∨ p2))) ∨ p5)) ∨ (True → (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207591674443883837396171774960 : (((((p3 ∧ p3) ∧ p5) → p3) → p4) → ((((p2 ∧ p2) ∨ (p5 → (((p5 → (True ∨ p4)) → False) ∧ False))) → (p5 ∨ (p5 ∧ p4))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p3 ∧ p3) ∧ p5) → p3) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611193511658826582963578564750 : (((((((p2 → p5) → p5) → (((p3 ∧ p3) ∨ p2) → (((False ∧ (True ∨ ((p3 ∨ (p2 ∨ p5)) → p5))) ∨ False) ∧ p4))) → p4) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329288071378632601488436439145 : (True → (((p5 → True) → p1) ∨ (p2 ∨ ((((p1 ∧ p3) ∧ ((p2 ∨ (p3 ∧ True)) → (p5 → (p4 ∧ True)))) → p5) ∨ (True ∨ (True ∨ False)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_89166427269105510406765078586 : ((((p2 ∨ p3) → p5) ∧ (((True → ((False → ((p4 ∧ p2) ∨ p5)) ∧ False)) ∧ ((True ∧ ((p2 → p1) → (False ∨ p3))) ∧ p5)) ∧ True)) → False) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h12 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h13 := h6 h12
  -- We need to get the right conjuct of h13 based on <expert-advice>.
  let h14 := h13.right
  -- False on the left can always be used.
  apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356375726483361774314364344259 : (p5 → (((p1 ∨ (False → (p1 ∨ ((p5 → p4) ∧ (p5 ∧ (p1 ∨ p4)))))) ∨ False) → ((((True → p4) ∧ (True ∨ (False → p2))) → p1) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320267695619810281937374216035 : (p4 ∨ ((False ∧ p1) ∨ (p4 ∨ (p4 → (p3 ∨ (True ∨ ((p4 ∧ p3) ∨ ((p3 ∧ (((p4 → p4) → p2) ∨ p1)) ∧ (False ∧ (True ∧ p4)))))))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148226288976215634078361290460 : ((((p3 ∨ (((p3 → (False ∧ p5)) → ((p4 ∨ (p2 ∨ p2)) → p4)) → p1)) ∨ p5) ∨ (p5 ∧ (p2 ∧ p2))) ∨ ((p1 ∧ p4) → (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159019305260797521567699654166 : ((p4 ∨ (((p2 → ((p3 ∧ (p3 ∨ False)) → (p4 ∨ p2))) → p2) → ((p5 ∧ (p5 ∧ p2)) ∧ p1))) ∨ (((True ∨ p2) ∨ (True ∧ p3)) ∨ p1)) := by
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
theorem thm_5_vars_191554016072769806139329261087 : ((p1 ∧ (p1 ∧ (((True ∨ (p1 ∨ True)) ∨ p2) → p1))) ∨ ((p1 ∨ True) ∨ ((((p1 ∨ (p1 → (p4 → p3))) → p4) ∨ p2) ∧ (p1 → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111605769366287105415497894962 : (((((p1 ∨ (p2 → ((p1 ∨ ((False ∧ (((p1 ∧ p5) ∨ (False → False)) ∨ p5)) ∨ True)) ∧ (p2 ∧ False)))) ∧ p2) ∨ True) ∨ p1) ∨ (p2 ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166330899045808861895265043571 : ((p5 ∧ ((p3 ∨ p4) → ((((p2 ∧ True) ∨ ((p5 → (p4 ∨ p2)) ∨ False)) ∧ p1) ∧ True))) ∨ ((p1 ∨ ((True → p2) → p2)) ∨ (p1 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244475889278803088830009383340 : ((False ∧ p2) ∨ (p1 ∨ (((p5 ∨ ((False → p1) → (p2 ∧ True))) ∨ (p1 ∨ p4)) ∨ (((False → (((p5 ∨ p3) → p3) ∨ p1)) ∧ True) ∨ False)))) := by
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
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138795411165178472335751632735 : ((((p2 ∨ p2) → (((p2 ∨ p1) ∧ p4) ∨ ((((p3 ∧ ((True ∨ p5) ∨ (True ∨ True))) → False) ∧ p2) → True))) ∧ p2) → ((True → False) → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65413664259056084517891179030 : ((p3 ∨ (((p1 ∧ p5) → False) ∧ (p3 → (p2 ∨ ((((False → p5) → p3) ∧ (p5 → ((((p1 → False) ∨ p4) → p2) ∨ False))) → p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337555006300773871032626392077 : (p1 → ((p2 ∨ ((((False ∧ False) → ((False → (p3 ∧ (p2 ∧ p4))) ∨ True)) → (False ∧ p4)) ∨ (True ∨ p3))) ∨ (((True ∨ False) ∨ p2) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148631542827115175862942025776 : (((p1 ∨ (p1 → ((p4 ∨ (False ∧ p4)) ∨ (False ∨ p4)))) → (p2 → ((p2 ∧ True) → (p3 ∨ (p4 → p5))))) ∨ ((p4 → (p3 ∧ p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606166279776529312496088571593 : ((((((((((p1 ∨ (p1 → (((p2 ∨ p2) ∧ p5) ∨ False))) ∨ p5) ∨ ((p2 ∧ p3) ∨ p4)) ∧ p5) ∧ (p4 ∧ False)) ∧ False) ∧ p1) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_184202989976676011712043266241 : ((((True ∧ ((p5 ∨ p5) → (p1 ∨ (p5 → p4)))) ∧ p2) → p1) ∨ (((p4 ∨ p4) → (((p5 → (p4 ∧ p4)) → p4) ∨ p4)) ∨ (p5 → p3))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608526989594330030022988071113 : (((((((False → p2) ∨ ((True ∨ ((((False → False) ∨ True) → ((True → p4) ∧ (p2 → False))) → (p4 → p1))) ∧ p3)) → False) ∨ p4) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_685401778780133829124172567119 : ((((((True → (True ∧ (p3 ∧ ((((p3 ∧ p3) ∧ p4) → p1) ∧ (p2 ∧ True))))) ∧ p1) ∧ p3) → (((p1 ∧ (p4 → p5)) ∧ True) ∨ p3)) ∨ p3) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351239366171808631271576153279 : (p4 → (((p1 ∨ ((p2 ∧ False) ∨ ((p1 ∨ p2) ∧ False))) ∨ ((p5 → ((True → (p3 ∧ p3)) ∨ (p3 ∧ p5))) ∧ p2)) ∨ ((p3 ∧ p2) → p2))) := by
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
theorem thm_5_vars_349397037930175577008254037554 : (p3 → (p4 → (((p4 → (p1 ∨ (False → True))) → (((p1 ∨ ((True ∧ ((p5 ∨ p2) ∨ False)) ∧ ((p4 ∨ True) ∨ p5))) → False) ∨ p3)) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134217412149553147062843899756 : ((((((True → p4) ∧ (p1 ∧ False)) ∨ p1) ∧ ((p1 ∧ ((p4 ∧ (p2 ∨ (True → True))) → p4)) ∨ (True ∧ p4))) ∨ p3) ∨ (p3 ∨ (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_665019644298021346516870232377 : ((((p4 → ((((p2 ∨ p5) ∧ p4) ∨ ((p3 ∨ p2) → p3)) ∨ ((p5 ∨ False) ∧ (((p1 ∨ p1) → p2) ∨ (p5 → p5))))) → (True → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711239102208876729200842064362 : ((((p4 ∧ (p1 ∨ ((p4 ∨ p1) → p1))) ∧ (((((True ∧ p2) ∨ p3) → p2) ∧ (p4 ∧ ((p1 → p1) ∨ p3))) ∨ ((p3 ∨ True) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345714898601586918083399485664 : (p3 → ((p2 → ((((p5 → p1) ∧ ((((True ∧ ((True → (True ∨ p3)) ∨ p4)) → False) ∧ (False ∧ True)) ∨ p4)) ∨ (p1 → p2)) ∨ True)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69782773318353078484071951238 : ((((((((p2 ∧ p1) ∨ p4) ∨ (True ∧ (p5 → ((True ∨ p3) ∨ ((p4 ∧ p5) ∧ True))))) → p4) ∧ (p3 ∨ (True → p5))) ∨ p4) ∧ p2) → p4) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h8 : (((p2 ∧ p1) ∨ p4) ∨ (True ∧ (p5 → ((True ∨ p3) ∨ ((p4 ∧ p5) ∧ True))))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Implications on the right can always be decomposed.
        intro h9
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h10 := h5 h8
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h12 : (((p2 ∧ p1) ∨ p4) ∨ (True ∧ (p5 → ((True ∨ p3) ∨ ((p4 ∧ p5) ∧ True))))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Implications on the right can always be decomposed.
        intro h13
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h14 := h5 h12
      -- One of the premise coincides with the conclusion.
      exact h14
  case inr h15 =>
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_15259467339205690567644030122 : (((p5 → ((((p5 → (p2 ∨ (p2 ∨ (p2 ∧ True)))) → False) → p2) → (((p1 ∨ p2) ∧ (p1 → p3)) → (True ∧ p4)))) ∨ (p1 → True)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166129236593735306179254010383 : ((True ∧ ((((p3 ∧ (p3 → p3)) ∧ p4) ∧ p4) ∧ (False → (False ∧ (p3 → (p5 ∧ p4)))))) ∨ (True ∧ ((((p3 ∨ p2) ∨ p5) ∨ True) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_613128642109145617281285345873 : ((((((p5 ∨ ((p1 → (p2 ∨ ((((p4 ∧ p1) ∧ ((p3 → (True ∨ p3)) ∨ p2)) ∧ False) → p5))) ∧ p1)) → p5) → (False ∧ p1)) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_114392269825992478578326391026 : ((((p4 ∨ (((((p3 → (p1 ∨ p2)) ∨ p3) ∨ p3) → p2) ∨ False)) ∧ ((p4 → p2) ∧ p5)) ∨ ((True ∧ p3) ∧ (p1 ∧ p1))) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264058633821514382841477029421 : (True ∧ ((((p1 ∧ (p2 ∨ p3)) ∨ (p1 ∧ (True ∧ False))) ∧ p4) ∨ ((True ∧ True) ∧ ((p2 ∧ (True ∧ p1)) ∨ (p3 → (p3 ∧ (True ∨ p3))))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148365259109344218730031867520 : ((((((((False → p5) ∧ ((False → p1) ∨ False)) ∨ p1) ∨ p1) → p5) ∧ True) ∨ (((True ∨ p5) ∨ p1) ∨ p4)) ∨ ((False → p2) ∧ (p2 ∨ False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_47217299130963688574892307407 : ((((((True ∧ (True ∧ (p5 ∧ p1))) → (p3 ∧ False)) ∨ p3) → ((((((False → p4) → True) → True) ∨ True) ∧ False) ∧ p3)) ∨ (True ∨ p5)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658489895375139217577304144454 : ((((p1 ∨ (p3 ∨ (False ∧ (((p4 ∧ p3) ∧ ((p3 → (p3 ∧ (p5 → (p4 → p1)))) ∧ ((p4 ∨ p5) ∨ p3))) → False)))) ∨ (p2 → True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_117027770983883647256248189025 : (((p2 ∨ p2) → ((p1 ∧ (p5 ∨ p1)) ∨ ((((p3 ∨ p5) ∧ ((p1 → p1) ∧ False)) ∨ (p3 ∧ (p1 → (p5 → p2)))) → True))) ∨ (p3 ∨ p1)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42900015536544069315312244414 : (((p3 → (((p1 → p2) → (False ∨ ((p3 ∧ p1) ∧ False))) ∨ ((p5 ∨ (p2 ∧ (p3 ∧ ((True ∧ p3) ∧ (p3 ∧ p1))))) ∨ False))) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319372887978178943266489652938 : (p4 ∨ (((p5 → (p4 → False)) ∧ ((p2 ∨ p1) ∨ (p3 ∧ ((True → p5) ∨ p1)))) ∨ ((p2 ∨ (True ∨ p1)) → ((p1 ∨ (False ∨ True)) ∨ p3)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
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
theorem thm_5_vars_725050372972060574496814526287 : ((((False → (True ∨ p5)) ∧ ((p5 → (((((p3 ∨ ((False ∨ p5) ∧ p5)) ∨ False) ∨ (p5 ∨ p5)) → False) ∧ (p2 ∨ (p4 ∧ p5)))) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39629297594692445779073442431 : (((p3 ∨ (((((p1 → (((p2 ∧ p3) ∧ True) ∨ ((p5 ∨ (p5 ∨ p2)) ∧ p1))) → (True ∧ p4)) ∧ p4) → (p5 → p3)) ∧ True)) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_203896061555602379964872777747 : ((p1 → (True ∧ ((p2 ∨ p1) ∧ p1))) ∧ (((p4 ∧ (True → p2)) → ((p5 ∨ (((p3 ∧ p3) ∧ p5) ∧ True)) ∨ p5)) ∨ (p1 → (False ∨ p1)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43342548572791502830910301866 : ((((((p4 ∨ True) → (((p4 ∧ (p2 ∧ ((((p2 ∨ (False → p5)) ∧ p5) → (False → p5)) ∨ p1))) ∧ True) ∧ False)) → p5) ∨ p1) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64729146115414403643501921587 : ((p1 ∨ (p5 → ((p5 ∨ p5) ∧ (p3 → ((p5 ∨ p5) ∧ (False ∨ (False ∧ ((True ∧ (p2 ∧ True)) ∨ (((p1 ∨ p5) → False) → p5))))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342163740929323083113279463468 : (p2 → (((((p2 ∨ p3) ∨ p1) ∨ p5) ∧ (p5 ∧ (((True ∨ p1) → (p1 → (False → p2))) → (False ∧ p1)))) ∨ ((p5 → p1) ∨ (p2 ∨ p3)))) := by
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
theorem thm_5_vars_791606730716490555549527762855 : (((True → (((p4 ∧ ((((p1 → p3) ∧ True) ∧ ((True ∧ ((True ∨ p1) ∨ ((p5 → False) ∨ p1))) ∧ (True → p5))) → p3)) → p5) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313962181242331969861090370723 : (p3 ∨ ((((True ∧ p4) → (((((p1 → p1) ∧ (p1 ∨ p4)) ∧ p1) ∨ (True → p1)) ∧ (p1 ∧ p2))) ∧ ((p5 ∧ p5) → p2)) ∨ (True ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699194801282050748114222825875 : ((((p2 → ((p3 ∨ p3) ∧ ((p4 ∨ (True ∧ p1)) ∧ (p3 → True)))) ∨ (False ∧ (p4 ∨ (((False ∨ p3) ∧ p1) ∨ (p5 → (p2 ∧ p2)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350796392016667490352637216878 : (p4 → (((((False ∧ ((p2 ∨ (p2 ∧ p1)) ∨ (True ∧ p3))) ∨ ((p5 ∨ ((p2 ∨ p3) ∨ (p4 ∨ True))) ∨ p5)) ∧ True) ∨ False) ∧ (False ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_920581798723459027252045774784 : ((((((p1 → False) ∧ (((p5 ∧ False) → p5) → p1)) ∧ (True ∨ (p5 ∨ p5))) ∨ ((((p2 → p2) ∧ p1) ∧ p5) ∧ ((p2 ∨ p2) ∧ p2))) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    cases h4
    case inl h7 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h8 : ((p5 ∧ False) → p5) := by
        -- Implications on the right can always be decomposed.
        intro h9
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- False on the left can always be used.
        apply False.elim h11
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h12 := h6 h8
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h13 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h12
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h14 := h5 h13
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h17 : ((p5 ∧ False) → p5) := by
          -- Implications on the right can always be decomposed.
          intro h18
          -- Conjunctions on the left can always be decomposed.
          let h19 := h18.left
          let h20 := h18.right
          -- False on the left can always be used.
          apply False.elim h20
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h21 := h6 h17
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h22 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h21
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h23 := h5 h22
        -- False on the left can always be used.
        apply False.elim h23
      case inr h24 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h25 : ((p5 ∧ False) → p5) := by
          -- Implications on the right can always be decomposed.
          intro h26
          -- Conjunctions on the left can always be decomposed.
          let h27 := h26.left
          let h28 := h26.right
          -- False on the left can always be used.
          apply False.elim h28
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h29 := h6 h25
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h30 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h29
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h31 := h5 h30
        -- False on the left can always be used.
        apply False.elim h31
  case inr h32 =>
    -- Conjunctions on the left can always be decomposed.
    let h33 := h32.left
    let h34 := h32.right
    -- Conjunctions on the left can always be decomposed.
    let h35 := h33.left
    let h36 := h33.right
    -- Conjunctions on the left can always be decomposed.
    let h37 := h35.left
    let h38 := h35.right
    -- Conjunctions on the left can always be decomposed.
    let h39 := h34.left
    let h40 := h34.right
    -- Disjunctions on the left can always be decomposed.
    cases h39
    case inl h41 =>
      -- One of the premise coincides with the conclusion.
      exact h40
    case inr h42 =>
      -- One of the premise coincides with the conclusion.
      exact h40
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328412045422257449015434032790 : (True → (((((p3 ∨ p3) → (((p5 → p1) ∧ (True ∨ p2)) → p1)) ∨ (True → p1)) ∨ (p3 ∧ p5)) ∨ (p2 → (True → ((p3 ∨ p3) ∨ p2))))) := by
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
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165631748328686206768803863601 : ((((False ∧ p1) ∧ ((p5 ∨ True) → p5)) ∧ ((((p3 → False) → p4) ∨ (p5 ∧ False)) ∨ p3)) ∨ (p3 → (((False ∧ (p5 ∧ p1)) ∧ p4) → p3))) := by
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
  let h5 := h3.left
  let h6 := h3.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113374264054508123581463454219 : (((p2 ∨ ((p1 ∧ ((True → (p3 ∧ p1)) → (p3 → (p5 ∧ True)))) ∧ ((p3 ∨ False) ∨ ((p4 ∨ p5) → p3)))) ∧ (True ∨ p1)) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620035521862955659454648282404 : (((((p4 → p1) ∧ (((((((p1 → False) → p3) ∨ (p1 ∨ (p2 ∧ ((p5 ∧ (p4 ∧ False)) ∧ True)))) → p4) → p2) ∨ p2) ∨ False)) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180648114431751957782749504141 : ((((p4 ∧ p2) ∨ (True ∧ (p4 ∨ True))) ∨ (((p4 ∨ p5) → p4) ∨ p2)) → (p4 ∨ ((False ∨ ((((False ∨ p3) → p2) ∨ True) ∨ p2)) ∨ True))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h11 =>
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
theorem thm_5_vars_112231893068176797467547825616 : (((p2 ∨ (((p1 ∧ ((((False ∨ p4) ∨ p4) ∨ p4) ∨ False)) ∨ ((p5 → (p5 ∧ False)) ∧ p4)) ∧ (p3 → (False ∧ p2)))) ∨ True) ∨ (p3 → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38802115614173382550878025584 : ((((((p5 ∨ p3) ∧ p4) ∧ True) → (p1 → (((p5 ∨ (True ∧ ((True ∨ (True ∨ p1)) ∧ p2))) → (p3 ∧ (True ∧ p2))) ∨ p3))) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47912291329277539288064450937 : (((((((p5 → p3) ∨ ((p2 ∧ True) → True)) → p1) ∨ ((p2 ∧ ((p1 → True) ∨ (p4 ∨ p2))) ∨ p1)) → (p1 ∨ p1)) → (p1 ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255254047279996626433785412663 : ((p4 ∧ p5) → ((p1 ∨ (((((p3 ∨ p3) → p3) ∨ p3) ∧ (False ∨ (p3 ∨ (((p1 ∧ (False ∨ p3)) ∨ p4) ∧ True)))) ∧ True)) ∨ (False ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304979726944956396653786843707 : (p1 ∨ (((p5 ∧ ((p4 ∨ (((p2 ∨ p4) ∧ True) ∨ (p5 ∧ ((p5 ∨ p2) ∧ ((False ∨ p2) ∨ p3))))) ∧ p1)) ∧ True) ∨ ((p5 → True) ∨ False))) := by
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
theorem thm_5_vars_66227921847379257271954257027 : ((p5 ∨ ((p5 → (((p1 → p1) ∧ p5) ∨ ((p2 → p5) ∨ p4))) → ((p4 ∨ (((p2 → ((p5 → p3) ∧ p1)) ∧ p3) → p5)) ∨ True))) ∨ p4) := by
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



