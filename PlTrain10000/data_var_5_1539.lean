variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60586167168500598641079615146 : ((True ∧ (((p2 ∧ True) → (((p4 ∧ p5) ∧ p2) ∧ (p5 ∧ ((p1 ∨ ((False → (True ∨ p2)) ∧ True)) ∧ (False → (True ∨ p1)))))) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112242303857546159077405514562 : (((p3 ∨ (((((p3 ∧ p5) → (p3 → (p1 ∧ ((p1 ∨ ((p2 ∧ p3) ∧ p1)) → p5)))) ∨ p5) → p5) ∨ (p2 ∧ p1))) ∨ True) ∨ (p4 → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693445235529130268911323970289 : ((((p5 → ((((p3 ∨ ((True → True) ∧ p1)) ∨ True) ∧ p2) ∨ (p2 → p4))) ∧ (((p5 ∧ p5) ∧ True) ∨ ((False ∨ p3) ∨ (p1 ∨ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_725163125697504178538478999290 : ((((p1 → (p2 → p3)) ∧ (((p3 → ((((((True ∨ True) → False) ∧ False) ∨ True) → (p1 ∨ (p1 → (p3 ∨ p2)))) ∧ True)) → p1) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191535150170967215242171666605 : ((p1 ∧ (((p1 ∨ ((True → False) ∨ p4)) ∧ p5) ∨ p4)) ∨ (p5 ∨ ((p1 ∧ ((p1 → (((False ∧ (p1 ∨ False)) ∨ False) ∧ p3)) ∧ True)) → p4))) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- False on the left can always be used.
    apply False.elim h10
  case inr h12 =>
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149533576314113796018098891384 : ((p2 ∧ ((((True ∧ (((p3 ∧ p5) ∨ p3) → p3)) → (True ∧ p2)) ∨ (True → (p1 ∧ (p1 ∨ p2)))) ∧ p4)) ∨ ((False → p1) → (True ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748571686022360464684907608912 : ((((p3 → False) → (p5 ∨ ((p1 ∨ p4) ∨ ((((((p5 → True) → p4) → p1) ∨ p5) ∨ (p1 ∨ False)) ∧ ((p4 ∨ p2) → (p5 ∧ p5)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135641764869955365964825736824 : (((((True ∧ ((p5 ∨ p1) ∧ (p4 → p1))) ∨ ((p4 ∧ p3) ∨ p4)) ∨ (True ∧ True)) → (((p2 ∨ p3) → p3) ∨ p1)) ∨ (True ∨ (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250918865900860355077815916850 : ((p1 → p3) ∨ (p1 → ((((p5 ∨ False) → (p2 ∧ True)) → ((True ∧ True) ∧ p2)) → ((p4 ∨ (p3 ∧ ((p1 ∧ p4) → (p4 ∧ p2)))) ∨ p1)))) := by
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
theorem thm_5_vars_164630554960142527686838582748 : (((p1 ∨ ((((p3 ∨ ((p2 → p1) ∧ p1)) → (p1 ∧ p2)) ∨ p1) ∧ (p2 ∧ p5))) ∧ False) ∨ (p1 → ((True ∨ p5) → (p5 ∨ (True ∨ True))))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173115076654378218678888571655 : ((p2 ∨ ((True ∧ (((p4 ∧ True) ∨ p3) ∧ ((p5 → False) ∧ True))) ∨ (p2 ∨ True))) ∨ (((p4 ∨ (p1 → p1)) ∨ (p5 ∧ p4)) ∨ (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225157140853291765386084656383 : (((p3 ∧ p4) ∧ False) ∨ (((((p3 ∧ p4) → True) → p3) → (p2 → ((p5 ∧ ((True ∨ (((p2 ∨ p5) ∨ p2) → p5)) ∨ p1)) ∨ p3))) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((p3 ∧ p4) → True) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_405906361751576701028279951979 : (((((p1 ∨ ((False ∨ ((((p5 → False) ∧ (True ∧ p4)) ∨ p1) ∧ True)) ∨ ((False ∨ p3) → (p4 → ((p3 ∧ False) → p2))))) → p2) → p2) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 ∨ ((False ∨ ((((p5 → False) ∧ (True ∧ p4)) ∨ p1) ∧ True)) ∨ ((False ∨ p3) → (p4 → ((p3 ∧ False) → p2))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h8
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68997905917826125544663009028 : ((p5 → (((p1 ∧ ((((True ∨ ((p2 → p1) → ((p5 ∨ (p1 ∨ p1)) ∧ p1))) ∧ p4) ∧ p1) ∨ p2)) → (True → (False ∧ p4))) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117249668168271074331393549884 : ((True ∧ (p5 ∨ ((((p1 → (p2 ∧ p4)) ∨ False) → False) → (p3 ∧ (p4 ∨ (True ∧ ((p3 ∧ (p3 → (p5 → p1))) ∨ p5))))))) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179398722992819318930377831449 : ((p3 ∨ ((p4 ∨ p2) ∨ (p3 ∧ (((True → p5) → p5) → (p5 → p1))))) ∨ (False → (p4 ∧ (p3 → (p3 ∧ (((p3 → True) → True) ∧ p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37472576820736314422835865566 : ((((((False ∨ (p3 ∨ p5)) ∧ (p2 → True)) ∨ ((p3 → ((((p5 ∧ p2) ∨ (True → p4)) ∧ p5) ∧ (p5 → p5))) ∧ p2)) ∨ p3) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181521646461657849066694647775 : ((True → (((p5 → ((True ∧ False) ∧ ((p3 ∧ p3) ∧ p4))) ∧ p5) → p3)) → ((((True → p4) ∧ False) ∨ (p5 ∨ False)) ∨ (p3 → (p2 → p3)))) := by
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
theorem thm_5_vars_171345326044089234074100129082 : (((((p2 ∨ (p1 ∨ (False ∨ p1))) → (False → ((p1 → p2) → True))) → False) ∧ p3) ∨ ((p1 ∨ p2) ∨ (True ∧ (False ∨ (p1 → (True ∨ p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165212230170345420662474197446 : (((((True ∧ (p4 ∧ p2)) ∨ (((p1 → p3) → p4) → p2)) ∨ (p5 → p3)) ∨ (False ∧ p3)) ∨ (((p1 ∨ ((True ∧ False) ∨ False)) → p1) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_661050762919570586075580767812 : ((((((((p3 → p3) ∨ p3) ∨ (False ∨ True)) → ((((p1 ∨ False) ∨ (True ∧ p4)) → (p3 ∧ True)) → False)) ∧ (p4 ∨ p2)) → (False ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_798274970444198190755280911463 : (((p1 → (((True ∧ (((True ∨ ((p5 → (p3 ∨ True)) ∨ p4)) ∨ False) → (p5 ∨ p2))) → p4) → (((p4 ∧ p4) ∧ p1) ∧ (p2 → True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50361192979848381315935580886 : (((((False ∧ p3) → p2) ∧ (p2 ∧ ((((p2 → p3) → (((p3 ∧ False) ∧ False) ∨ True)) → p5) → p2))) ∨ ((p4 ∨ p4) ∨ (False → p2))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323891610723911988499700431628 : (p5 ∨ (((((p5 ∨ p3) → ((p4 → p2) ∧ (p5 ∨ p5))) ∧ (p2 ∨ (False ∧ True))) → p4) ∨ (False → (((p3 → (p1 ∧ False)) → True) → False)))) := by
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
theorem thm_5_vars_733962349496688616780926170665 : ((((True ∨ False) ∧ (p1 ∧ (((True ∧ p3) ∧ (((((p5 → (p3 → ((p1 ∨ True) → p4))) ∧ p2) ∨ (False ∧ p5)) → p1) ∨ False)) ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52081671875046580134807995969 : ((((p4 ∨ ((p2 ∨ ((p2 → (p2 ∧ (p2 ∧ p1))) → False)) → (False ∨ p3))) ∧ True) → (((p3 ∧ p4) ∨ ((p3 ∨ p1) ∧ p2)) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311043681495409077415822701004 : (p2 ∨ ((p4 ∧ p1) ∨ (((p2 → (p3 ∨ ((p3 ∧ p4) ∨ (p5 ∨ ((p2 ∧ p2) ∨ p2))))) ∧ (p2 ∨ (True ∨ p4))) ∨ (p1 ∨ (True ∨ p1))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609982820301385825465399634490 : ((((((((p3 → (p1 ∨ p1)) ∧ (((True ∨ p4) ∨ p1) → (p1 ∨ (((p1 ∧ p5) ∧ p4) ∧ (p4 → False))))) ∧ p5) ∧ p1) → False) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_600877809364878598055662834367 : ((((False ∧ (p5 → ((p2 → (p3 → ((((((p5 ∨ p3) ∨ p4) ∧ p5) ∧ p1) ∨ p3) ∧ (p1 ∧ p2)))) ∧ ((p5 → p2) ∨ p3)))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_598819206733762059612409332546 : (((((p3 ∧ p1) ∧ (((p5 → (False → (((((p5 ∧ p1) ∨ False) ∧ p5) ∧ ((p3 → (True ∨ p1)) → False)) ∧ False))) → p4) ∧ p3)) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339980501438840157807545377299 : (p1 → (p1 → (((p5 → (p1 → (((((p4 ∧ (p1 ∨ False)) → p5) → p4) ∧ p4) ∨ p5))) → (((p4 → p1) ∧ p4) ∧ False)) → (p5 → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : (p5 → (p1 → (((((p4 ∧ (p1 ∨ False)) → p5) → p4) ∧ p4) ∨ p5))) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h8 := h3 h5
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305563789146492352448472159377 : (p1 ∨ (((False ∧ (p1 ∨ p1)) → ((False ∨ ((p4 ∨ p4) ∨ p4)) ∨ True)) ∧ (p4 ∨ (((False ∧ p5) ∧ False) ∨ ((False ∨ p2) ∨ (False → p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749484322811926732137922717854 : (((True ∧ (((p2 → (False ∧ (p5 ∨ p5))) ∨ ((p3 → (p1 ∨ p4)) → (p3 → ((True ∧ p4) → (True ∧ (p1 ∧ (p2 ∧ True))))))) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44401929860051078184466271066 : (((((p3 ∨ ((((p3 → p2) → (p4 ∨ (False ∨ p3))) ∨ p1) ∨ p5)) ∧ p2) → (((True ∨ p5) → ((p2 → p3) ∧ p3)) ∨ p4)) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198162067809103892210526916024 : (((p1 ∨ False) → (((False ∧ p5) ∧ p5) ∨ p2)) ∨ ((((((p5 → p5) → False) ∨ (True → (p1 ∧ p5))) ∨ True) ∨ (p4 ∨ p1)) ∨ (p5 ∨ p1))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55369095158135290528490827438 : ((((((p2 ∨ p5) ∧ p2) ∧ p1) ∧ p4) → ((False ∧ (((p2 ∧ True) ∧ (p2 ∨ p5)) ∨ (p5 ∧ p5))) ∧ (p2 ∧ ((True ∨ p3) → False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_629743703745416585693295500188 : (((((((True ∨ (p3 → (p3 ∨ p3))) ∨ ((p2 → False) ∨ ((False → p5) ∨ True))) ∨ ((False ∧ p2) → ((p5 ∨ p2) → True))) ∨ p2) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156947755024914189552719265640 : (((((True → (p4 ∨ (p3 ∧ p2))) → ((p4 → p5) ∨ (True ∧ (p3 → False)))) → (p3 ∨ p2)) ∨ p5) ∨ (True ∨ ((False ∨ (p4 ∨ True)) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601806152639159683529322958880 : ((((p4 ∧ ((((p2 ∧ (((((True → (p4 → p1)) → p4) ∨ (p3 ∨ p3)) ∧ p1) ∧ p3)) → False) ∨ p4) ∧ (p2 ∧ (p1 → p4)))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134314132039623471914867310637 : (((False ∧ (((((False ∧ False) ∨ (p1 ∨ p4)) ∨ (p3 → p3)) ∨ p4) → (((p2 ∨ (p5 → p2)) → p5) ∨ p3))) ∨ True) ∨ ((p5 ∧ p3) ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172650007848996019646460048494 : (((p3 ∨ p2) ∧ ((p4 ∨ p3) ∧ (((False → p3) ∧ (False ∨ p4)) ∨ (p1 ∨ p2)))) ∨ ((p4 ∧ p4) ∨ (((p1 ∧ (p3 → False)) ∧ True) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226298880023509808083146981328 : (((p4 ∨ p4) ∨ False) ∨ ((p4 ∨ (((False ∨ (((True → p5) ∧ p4) ∨ p1)) ∨ p3) ∨ (p5 → p2))) ∨ ((p3 ∨ (p2 ∧ True)) ∨ (p1 → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140774142451152468802205678812 : ((((True ∨ (((((False → p4) → p4) → p1) ∧ p1) ∧ p2)) ∧ p4) ∧ (True ∧ (((p1 ∨ p3) ∧ (False → p2)) ∨ True))) → ((p4 → True) → p4)) := by
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
  cases h5
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h4.left
    let h9 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h13 =>
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h14 =>
        -- One of the premise coincides with the conclusion.
        exact h6
    case inr h15 =>
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- Conjunctions on the left can always be decomposed.
    let h19 := h17.left
    let h20 := h17.right
    -- Conjunctions on the left can always be decomposed.
    let h21 := h4.left
    let h22 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h23 =>
      -- Conjunctions on the left can always be decomposed.
      let h24 := h23.left
      let h25 := h23.right
      -- Disjunctions on the left can always be decomposed.
      cases h24
      case inl h26 =>
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h27 =>
        -- One of the premise coincides with the conclusion.
        exact h6
    case inr h28 =>
      -- One of the premise coincides with the conclusion.
      exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46605710888197922911774500127 : (((p2 ∧ ((p4 ∧ ((p1 ∨ ((p5 ∧ False) ∨ ((False ∧ p4) ∨ False))) ∨ ((p4 → p2) ∨ p5))) ∨ ((p4 ∨ p4) ∨ True))) ∧ (p2 ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48163049841034043369388067413 : ((((p5 ∧ p3) ∧ ((p4 ∧ p3) → (True → (((p3 → p5) ∨ (p4 → (p3 → p3))) → ((p5 → p4) ∨ (p2 ∨ False)))))) → (p4 ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168204852107845448466552014643 : ((((p3 ∨ p5) → True) ∨ ((((((p4 → (True → p4)) → p2) ∨ p3) ∨ p4) ∧ False) ∨ p2)) → ((p1 → ((p5 → True) ∧ False)) ∨ (True ∨ False))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- False on the left can always be used.
          apply False.elim h6
        case inr h9 =>
          -- False on the left can always be used.
          apply False.elim h6
      case inr h10 =>
        -- False on the left can always be used.
        apply False.elim h6
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140511163571555184131154689139 : ((((False → p5) ∨ ((True → (((((p1 ∧ p2) ∧ p4) ∨ p1) ∧ p1) → False)) ∨ p2)) ∧ (p1 → ((p4 ∨ p3) ∨ p5))) → ((p2 ∧ p4) ∨ True)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158039888431526133305410411902 : (((((p1 ∧ p1) ∧ (False ∨ p1)) ∨ False) ∨ (((p2 ∧ (p1 → p2)) → (p3 → False)) → (False ∨ p3))) ∨ (p4 → (((p3 → p4) ∧ p3) → p4))) := by
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
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656137017410288849360797503268 : (((((p5 ∨ (((p5 ∨ ((p2 → p5) ∨ False)) ∨ (p4 ∧ (p3 ∨ p5))) ∧ True)) ∧ (False → ((p4 → (p1 ∧ p2)) ∧ p1))) ∨ (False ∨ True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_141957374189030471909168546912 : (((True ∨ p3) → ((p1 ∧ p5) ∧ ((((p1 ∧ (p5 ∨ True)) ∧ (p3 ∧ p5)) → ((p5 → (True → p4)) → False)) ∧ False))) → (p3 ∧ (p1 ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : (True ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785983152802203533769073584550 : (((p4 ∨ ((((p2 ∧ p2) ∨ p1) ∨ (p3 ∧ (((((p4 ∧ p4) → (p3 ∧ p5)) ∨ p1) ∨ p4) ∨ ((p3 ∧ p3) → True)))) ∨ (False → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_647561880120648617894764121799 : ((((p5 → ((((((((p2 → (p2 → False)) ∨ (p1 ∨ p2)) ∧ p3) → True) → (p1 → p2)) ∨ False) → ((p3 ∧ p4) → False)) → p5)) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121763194878614293145538814679 : (((((p3 → (p5 ∨ False)) → p3) → (((p2 ∨ (((p1 ∨ p1) → ((True ∧ (False ∧ p1)) → p3)) → False)) ∧ p1) ∨ True)) → False) → (False ∧ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p3 → (p5 ∨ False)) → p3) → (((p2 ∨ (((p1 ∨ p1) → ((True ∧ (False ∧ p1)) → p3)) → False)) ∧ p1) ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : (((p3 → (p5 ∨ False)) → p3) → (((p2 ∨ (((p1 ∨ p1) → ((True ∧ (False ∧ p1)) → p3)) → False)) ∧ p1) ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h5
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150212885743015234937031499734 : ((p2 → ((p2 → ((p3 → False) ∨ True)) → ((((p5 ∧ (p5 ∨ p5)) ∧ False) ∨ (p3 ∧ (True → p1))) ∧ p5))) ∨ (True ∨ (p1 ∨ (False ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317632423275881077156976693050 : (p4 ∨ ((((p3 ∧ ((True ∧ p3) ∧ (p2 ∨ ((False → p3) ∧ False)))) ∨ ((True ∨ p4) → (((False ∨ p5) ∨ p2) ∨ (p4 ∨ False)))) ∨ True) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57505834586372318294919605611 : (((p3 → (p2 ∧ True)) ∨ ((((p3 ∧ (False → ((p3 ∨ False) ∧ (((p3 ∧ p2) → p1) ∨ p5)))) ∨ p4) ∨ (False ∨ p2)) → (p4 ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114133037963439416304243607420 : ((((((False ∨ ((p1 → (p5 ∨ (((p5 ∧ False) ∧ p5) ∨ p3))) → (p5 ∧ p4))) ∨ p2) ∨ False) ∧ True) → (p1 ∨ (False ∧ False))) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63986446609052623853677893028 : ((False ∨ (((p4 ∨ p1) ∨ ((((True ∨ p2) ∧ (True ∨ True)) → ((p2 ∧ (p2 → ((p1 ∧ p1) ∨ (p4 → p2)))) ∨ p4)) ∧ True)) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315904023954886661335792756131 : (p3 ∨ (True ∧ ((p2 ∨ (((p3 ∨ False) ∧ (p1 ∨ (p5 ∨ p3))) ∨ False)) ∨ (((False ∨ ((p1 ∨ (p4 → p3)) → p4)) ∧ p1) → (p3 ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179628896975486868560878848652 : ((p4 → (((p3 → (p2 ∧ p3)) ∨ p4) → ((p3 ∨ p5) → (p2 → p5)))) ∨ ((p5 ∧ p2) → ((p5 ∧ (p2 → (p2 ∧ p2))) ∨ (p1 ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708693518365721234364860813174 : ((((((((p1 ∨ p3) → False) → True) → False) → p2) → (p2 ∨ (((p1 → p1) ∧ p3) ∧ ((True ∧ ((p3 ∧ p3) → (p2 → p5))) ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114490550865653677061717538079 : (((((p3 ∧ (p3 → ((True → p4) ∨ (p3 → p3)))) ∨ p2) ∨ (p1 → ((False ∨ p1) ∨ True))) → ((p1 → p1) → (p1 ∨ False))) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319402494512486713731965335044 : (p4 ∨ ((((p4 → p2) ∨ p4) ∧ (p3 ∧ (((p2 → p5) → p3) ∨ (True ∨ False)))) → ((False ∨ True) ∧ ((False ∧ p5) → ((p3 ∧ p1) → p4))))) := by
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
    let h5 := h3.left
    let h6 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- False on the left can always be used.
        apply False.elim h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h3.left
    let h13 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h17 =>
        -- False on the left can always be used.
        apply False.elim h17
  -- Implications on the right can always be decomposed.
  intro h18
  -- Implications on the right can always be decomposed.
  intro h19
  -- Conjunctions on the left can always be decomposed.
  let h20 := h19.left
  let h21 := h19.right
  -- Conjunctions on the left can always be decomposed.
  let h22 := h18.left
  let h23 := h18.right
  -- False on the left can always be used.
  apply False.elim h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218925823362037098436236151762 : ((p3 ∧ (p2 ∧ (False → False))) → (p4 ∨ (((True → p2) → False) → ((p1 → p4) → (False ∨ (((False ∨ (p5 ∨ False)) → True) → (p1 ∧ p3))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h8 : (True → p2) := by
    -- Implications on the right can always be decomposed.
    intro h9
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h10 := h6 h8
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617812566073975071024525410621 : ((((((p3 → ((True ∨ p3) ∨ p5)) ∧ p5) → (p4 ∧ (((p3 → (((True → p5) ∧ p2) ∨ p1)) ∨ (p5 ∧ (True ∧ p1))) → False))) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_76494778209734345698142168001 : ((((p4 ∧ ((p2 ∨ ((((p3 ∧ False) → p2) ∧ p4) ∨ ((p5 ∨ p3) ∨ p2))) → (p4 ∨ (p4 ∨ p2)))) ∨ (p3 → (False ∨ p3))) → False) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p4 ∧ ((p2 ∨ ((((p3 ∧ False) → p2) ∧ p4) ∨ ((p5 ∨ p3) ∨ p2))) → (p4 ∨ (p4 ∨ p2)))) ∨ (p3 → (False ∨ p3))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135224885188010913046103483530 : ((((p5 ∨ (((p4 ∧ p4) → p3) → (p2 → p5))) ∧ (((p5 → (p1 ∧ True)) ∧ p4) → (p5 ∧ p2))) → (p4 ∧ p3)) ∨ ((True ∧ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56804994691148341096959292030 : ((((p2 ∨ p3) → p3) ∧ ((p3 → p2) ∨ (((((p2 → True) → ((p5 ∨ ((p1 → p2) ∧ p2)) ∧ True)) ∨ False) ∧ p3) ∨ (p2 ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137335233760513503433011840771 : ((p2 ∧ (p1 ∨ ((True → (p1 ∨ p5)) ∧ (True ∨ (((p3 → (p1 ∧ (p3 ∨ p2))) ∧ (p5 → (p4 → True))) ∨ p4))))) ∨ ((True ∧ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119604534303518584389950846016 : ((p5 → (p1 ∨ ((((p4 ∨ ((True ∨ (False → True)) ∨ (p2 → p4))) ∨ (((p3 ∧ p1) ∧ p3) ∧ (p3 → p5))) ∨ p2) → False))) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350022773717189471849779901287 : (p4 → (((((p1 ∧ (p3 → (True ∧ p3))) ∧ ((p3 ∨ p3) ∨ ((p1 ∨ (p1 → (p5 → ((True → True) → p5)))) ∧ p3))) → p2) → False) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121719246371793636737543517869 : ((((p5 → (((p3 ∧ (True ∧ True)) → p1) ∧ False)) → ((True → (((p1 → p5) ∧ (p3 ∨ (p4 → p2))) ∧ True)) ∨ True)) → p5) → (p5 ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p5 → (((p3 ∧ (True ∧ True)) → p1) ∧ False)) → ((True → (((p1 → p5) ∧ (p3 ∨ (p4 → p2))) ∧ True)) ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172658313750832333246760009198 : (((True → False) ∧ (p5 → (((p5 ∧ (p4 ∧ p1)) ∨ True) ∨ ((p2 ∧ True) ∧ False)))) ∨ (p2 ∨ (((p1 ∨ True) ∨ (p4 ∨ p1)) ∧ (p2 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135563940779888660489706059282 : (((p5 ∨ (True ∧ (p3 ∨ (False ∧ (p3 → (p2 → (((p1 → p3) ∧ p3) → p2))))))) ∧ (p3 ∧ (True → (p3 → p5)))) ∨ (False → (False ∧ p2))) := by
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
theorem thm_5_vars_69379210486047538464845235303 : ((p5 → (p1 → (((((p5 ∧ (p3 ∨ p2)) ∨ ((True → False) ∧ p5)) ∧ ((p4 → (p2 ∧ (p3 ∧ (False ∨ False)))) ∨ p2)) ∨ p1) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_687547694221157616200433574670 : (((((((p2 ∧ ((p4 ∨ True) ∨ ((p3 ∨ (True ∧ False)) ∨ p4))) ∨ True) ∨ p2) → p3) ∧ ((True ∨ p5) ∧ (((p3 ∧ p3) ∨ p5) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_90940571167108028445579503273 : (((True → p3) ∧ (p4 → (((((p1 ∧ p1) → p4) ∨ (((p3 ∨ p5) ∨ (p1 ∨ ((p5 → p3) ∧ True))) ∨ (False ∨ True))) → p3) → True))) → p3) := by
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
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305797454041855249072874049840 : (p1 ∨ ((((p5 → ((p1 → False) → p5)) ∨ p2) → p1) → (p1 ∨ (((p2 ∧ (p3 → False)) ∨ True) ∧ ((p5 ∨ (p1 ∨ (p3 ∧ p4))) ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p5 → ((p1 → False) → p5)) ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_80381672897855779387649315871 : ((((((p3 ∨ p5) ∨ p5) ∨ ((p5 ∨ (p3 → False)) → (False ∨ p2))) ∨ ((p5 ∧ p3) → ((True ∨ True) → (False → True)))) → (False ∧ p2)) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p3 ∨ p5) ∨ p5) ∨ ((p5 ∨ (p3 → False)) → (False ∨ p2))) ∨ ((p5 ∧ p3) → ((True ∨ True) → (False → True)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224273119988219762525092354842 : ((False → (False ∧ p5)) ∧ ((p4 → True) ∧ ((((((((p3 ∧ p1) ∨ p5) ∧ p3) ∨ False) ∧ False) ∨ (p2 ∧ p4)) ∧ (p3 ∨ p5)) ∨ (True ∨ p3)))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_719261212339330115446460263851 : ((((p4 ∧ ((p4 ∨ True) ∧ p4)) ∨ ((p3 ∨ ((p3 ∧ p3) → (p1 → ((p5 ∨ p2) → (p2 ∨ ((True ∨ (p3 → p2)) → p3)))))) ∨ p5)) ∨ p3) ∧ True) := by
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
    -- Implications on the right can always be decomposed.
    intro h7
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h1.left
    let h12 := h1.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205286023008167387003537632394 : (((p1 ∧ (p4 ∧ p5)) ∨ (False ∧ True)) ∨ (((p3 ∧ ((p4 ∧ p3) → True)) ∧ ((p3 ∨ (p4 → p1)) → False)) ∨ (p2 ∨ (p2 → (False → False))))) := by
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
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_25466877941703690443344573796 : (((p4 ∧ (False ∨ p1)) → (((((((p1 ∧ p2) ∧ ((True ∧ ((True ∨ p5) ∧ p5)) ∨ p4)) ∨ (p1 → p3)) ∨ p5) ∧ p2) ∨ p5) ∨ p1)) ∧ True) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61459323494440350474846990062 : ((p1 ∧ ((((((p3 → (p2 ∨ (False → (((False ∨ (p5 → p4)) ∨ p2) ∨ (p5 → p2))))) → p5) ∨ p1) ∧ p2) ∧ p4) ∨ (p3 ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350095779512796501082656347872 : (p4 → (((((True ∧ p4) → False) ∨ (((((p3 → p4) ∨ p3) → False) ∧ (True → p1)) ∨ ((p1 ∨ p1) ∧ p4))) ∨ (p4 ∨ (p1 → True))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_691272249899531189437661550696 : (((((((p1 ∨ p3) ∨ p4) ∧ False) → (((p1 ∨ p1) ∧ (p4 ∨ p1)) → (p1 ∧ p1))) → (True ∧ (((True ∧ p4) ∧ p3) ∧ (p5 → p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56595364350302987682773527106 : (((p3 → ((p1 ∨ p2) → p1)) → (((((p3 → (p3 → p3)) → p3) ∨ p3) ∧ ((p3 → True) ∨ (p1 ∧ (p1 ∨ (p5 ∨ p3))))) ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344844532322779830819365055917 : (p2 → (p5 → ((((((((p3 ∧ (p1 → p2)) → (p2 → p4)) ∨ p5) ∧ ((False ∨ p2) → p3)) ∧ p5) ∧ (p1 → p1)) → False) ∨ (p2 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_170037691794199614647348662366 : (((p4 ∧ (p2 ∧ ((True → (p4 ∧ p2)) ∧ (False → p4)))) ∨ ((p2 ∨ p5) → True)) ∧ ((p4 ∨ ((p5 → (p4 ∧ p2)) ∧ (p5 ∧ p5))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57202920926156861233319145834 : ((((p5 ∨ p5) ∨ p5) ∨ ((((p2 ∧ p4) ∨ (p4 → (True → False))) → ((False → p2) ∧ ((p1 ∧ (p1 → p4)) → (p3 → p4)))) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173476034777020560717504677067 : ((((p4 → (((p1 → False) → (p2 ∧ ((p3 → p2) ∧ True))) → False)) ∨ p4) ∧ p1) → ((p4 ∧ (((p4 ∨ (p4 → p1)) ∧ p3) ∨ p3)) ∨ True)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135323250728328167117979350796 : ((((((p2 → ((p5 ∨ p4) ∧ False)) → p1) ∧ (p2 → p1)) ∧ ((p2 ∨ True) ∧ (p3 → p3))) ∧ (p4 ∨ (p5 ∨ p2))) ∨ (p2 → (True → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173846014250253590031304569653 : (((p3 → (((p2 → (p5 → ((p4 ∨ (p2 ∨ p5)) → p1))) → p1) ∨ p4)) ∨ p3) → ((p2 ∧ ((p3 ∨ p4) → p5)) ∨ (p5 → (p1 → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257074999937906174003747879200 : ((p2 ∨ False) → (((((p1 → p2) ∧ p5) ∧ (p2 ∧ (True ∨ (((p2 ∨ ((False ∧ p3) ∨ (False ∨ p4))) ∨ p1) ∨ p3)))) → False) ∨ (p4 → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69075954346265601218164509815 : ((p5 → ((((p2 ∧ (p5 ∨ False)) ∨ ((((False ∧ (p2 → ((True ∨ p3) ∨ p2))) ∨ p5) → p2) ∨ False)) ∨ ((p2 ∧ True) ∨ p1)) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63943678732166917890680674703 : ((False ∨ ((((p3 ∧ False) ∧ p2) ∧ ((False ∨ (p5 → (p5 ∨ ((p1 ∨ True) ∧ (True → ((p3 ∨ (False ∨ False)) → p5)))))) → p3)) ∨ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_950138611271913530844586948214 : (((((p3 ∨ True) → p3) ∧ ((p2 → ((((True → (p1 ∧ p5)) ∨ True) ∨ (True → (p1 → False))) → (p3 → (p4 ∧ p1)))) → (p1 ∨ p5))) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p3 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720057501336343658100295256014 : ((((((True ∧ p1) → p5) ∧ p5) → ((p3 → (False ∧ ((p4 → (p2 ∨ ((True → p2) ∨ (p1 ∨ p3)))) ∧ p4))) ∨ (p5 ∨ (p3 ∨ p5)))) ∨ p3) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309606043107047728962500604044 : (p2 ∨ ((((((p1 ∧ (False ∧ p2)) ∧ (True ∨ (p4 ∨ (p1 ∧ (False ∨ True))))) ∧ (False ∧ p5)) ∨ (p1 ∧ False)) ∨ p3) ∨ (p5 → (True ∨ p5)))) := by
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
theorem thm_5_vars_661525671742409442486050877463 : (((((((p5 ∧ ((True ∧ ((p2 ∧ True) ∧ p4)) ∧ p5)) ∨ ((False ∨ (True ∧ True)) ∨ p3)) ∨ p4) ∨ ((p1 ∧ p2) ∧ p4)) → (False ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



