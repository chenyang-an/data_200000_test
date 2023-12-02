variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197018621488782395349282225036 : (((((p5 → p1) → False) ∨ (p1 ∨ p3)) ∨ p2) ∨ ((((p4 ∧ p3) ∨ (True ∨ (p5 ∨ (p1 → (p3 ∨ (p3 → (p3 ∧ p1))))))) ∨ p3) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_117404423230431997911861366154 : ((p1 ∧ (((p4 ∧ ((p5 → (p3 ∧ (p2 ∧ (False ∨ ((p5 ∨ p1) ∧ (p2 → p4)))))) → ((False ∨ True) ∧ False))) → p3) → p5)) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259141890641387757279913782275 : ((False → True) → (((True → ((p5 ∧ p5) ∨ True)) ∧ (((False ∧ False) ∧ (True ∧ (True → ((p1 ∨ (False ∨ p1)) ∨ False)))) → p3)) → (p3 → p3))) := by
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
theorem thm_5_vars_56157679042677005823110939144 : (((True ∧ (p5 ∧ (p3 ∧ False))) ∨ (p1 → (p2 ∨ ((False ∧ (p5 ∧ ((False → (p3 → (False ∨ ((p3 → True) → True)))) ∧ p5))) ∨ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56446203647906724110265792090 : ((((False ∨ p4) ∨ (p2 ∨ False)) → (p3 ∨ ((True ∧ ((False ∧ p2) → p1)) → ((((p2 → p4) ∧ (True → True)) ∧ False) ∧ (True ∨ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336369845889668442349180382968 : (p1 → (((False → p5) → (((p2 ∧ p1) → ((((p4 ∧ p2) ∨ p4) ∨ ((True ∧ p3) ∨ (p4 ∨ False))) ∨ p4)) → (p5 ∧ (p5 ∨ True)))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258845608846384764172641619187 : ((True → p1) → ((((((p4 ∨ (p2 ∧ p4)) → p2) → (p1 → p2)) ∧ (False → False)) → p1) ∨ (p5 ∨ (p3 ∧ ((p2 ∨ (p1 → p5)) ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658596487597293955728411747067 : ((((p3 ∨ ((True ∧ (p1 → (p3 → (p1 ∧ ((p5 ∨ (p1 ∧ p5)) ∧ ((p4 → p1) ∨ (p5 ∧ (p2 ∧ p4)))))))) → False)) ∨ (p4 → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173303158717737683813711626309 : ((p1 → ((False ∨ p4) ∧ (((p4 ∧ p4) ∨ p2) ∨ ((p4 ∧ p4) ∧ (p4 ∨ p3))))) ∨ ((False ∧ (p2 ∧ (p5 ∧ (p1 ∧ (p4 ∨ p2))))) → p5)) := by
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
theorem thm_5_vars_204105191060872409565835263952 : (((((p2 ∨ p2) ∧ p2) ∧ True) ∧ p4) ∨ (((p4 ∧ (p3 ∧ (p5 ∨ ((p5 → p1) → (True → p1))))) ∧ (False ∨ ((p4 ∨ False) ∨ p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3403425121884111723686289526 : ((p4 → p5) → (True ∧ (((p4 ∨ ((p5 ∧ p4) ∧ (p2 ∧ True))) ∧ p5) ∨ (p1 ∨ (p4 → (((False → p2) ∨ p5) → (False → p5))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51490827731822587130127885248 : (((((p3 → (p3 → True)) → p4) ∨ ((True → ((False ∨ p1) ∧ p5)) ∨ ((True ∧ p4) ∨ p4))) → ((p5 ∨ True) ∧ ((p3 ∧ p3) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232190726101324626771031950535 : (((False → p1) → p5) → (p4 → ((True → (True ∧ True)) → ((((p2 → ((True ∨ p3) ∧ p4)) ∨ p3) → p5) ∨ (p1 ∨ (p4 → (p2 ∧ p5))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h6 : (False → p1) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- False on the left can always be used.
      apply False.elim h7
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h8 := h1 h6
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h10 : (False → p1) := by
      -- Implications on the right can always be decomposed.
      intro h11
      -- False on the left can always be used.
      apply False.elim h11
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h12 := h1 h10
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_793133596483478381514026941262 : (((True → (True ∧ ((((p2 ∨ ((p2 ∨ False) ∨ ((p5 → ((p5 → p3) ∧ True)) ∧ (True ∨ (p3 ∧ p1))))) → (True → p3)) ∨ False) ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50335559196937163736766845127 : ((((((False ∧ p4) ∧ p5) → ((False → False) → p3)) → (p1 ∧ ((p2 ∨ (p5 ∧ p1)) → (p4 ∨ False)))) ∨ (p2 ∨ ((p5 ∨ p1) ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47195809640115955712138850153 : ((((p3 ∨ (p2 ∨ ((p2 ∧ ((p2 ∨ (False ∧ p2)) → False)) ∨ p4))) ∨ (False → (p3 ∧ (False ∨ ((p5 ∨ p1) ∧ p4))))) ∨ (True ∧ p1)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_654722738876989367140898485402 : ((((((((False ∧ p5) ∨ p5) ∧ ((((p4 ∧ p1) ∧ p1) ∨ p2) → (((p5 ∨ False) → True) → (p3 ∨ True)))) ∨ p1) → p2) ∨ (p4 ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_743123818531443168262807187082 : ((((p4 → p2) ∨ (((p2 ∧ (False → (p1 ∧ ((p1 ∧ p5) ∧ p4)))) ∨ False) ∨ ((p1 → (((p5 ∧ p1) ∧ p2) ∧ p5)) ∨ (False ∧ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261497408514748169067070597537 : ((p5 → p3) → ((((p4 ∧ ((False → (p5 ∧ True)) ∧ ((True → (p1 ∧ p2)) → (p3 ∨ False)))) ∨ p2) ∨ (p4 ∧ ((False ∧ p4) ∨ True))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171571910048281709289094689194 : ((((((True ∧ ((p1 → p3) → (p2 ∨ False))) ∨ p5) ∧ p1) ∨ (p3 → True)) ∨ p1) ∨ (((False ∧ (p4 → (p1 ∧ p3))) ∧ (p5 ∧ p2)) ∨ p3)) := by
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
theorem thm_5_vars_156802601038618448231741376602 : (((p5 ∧ (p5 → (False ∧ (p3 ∨ ((p5 ∨ p2) → (((False → True) → p2) ∨ (p2 ∨ p3))))))) ∧ p3) ∨ (p2 → ((False ∧ (p4 → p3)) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_149904022492125908015531736829 : ((p2 ∨ (p3 → (p4 ∨ (p1 ∧ (True → (((p5 → p3) ∧ p4) → (((False → False) → (p2 → True)) ∨ True))))))) ∨ (((True ∨ False) → False) → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125244755932419102671805486453 : (((p5 → (p1 → p2)) ∨ (p3 ∧ ((p4 ∨ ((True → ((p1 → ((p5 ∨ (p2 ∨ p3)) → (p2 → True))) ∧ p4)) ∨ p5)) → p1))) → (p2 → p2)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64794523850829978007567608306 : ((p2 ∨ ((((p3 ∨ p5) ∧ p1) ∨ ((((p3 → p5) ∨ p4) ∧ True) → (p4 ∨ ((p1 ∨ (p2 ∨ p3)) ∧ ((True → False) ∧ p3))))) ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2597637029348594778639213227 : ((True ∨ (p5 → (p3 → ((p1 ∧ p2) ∧ p2)))) → (((p2 ∨ (p3 ∧ ((True → (False → (False ∨ p1))) ∧ p5))) ∨ (False → p3)) ∨ p2)) := by
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214075805487280739937935655438 : ((((False ∧ p1) ∨ p5) → p4) ∨ ((((((p1 → p4) ∨ (p1 ∨ (p2 → (p1 → False)))) → (p4 → p1)) → (p4 → p3)) ∨ (p4 → p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638378007680844463436175970401 : ((((((False ∨ p1) → ((p4 ∨ p2) ∨ p4)) ∧ (((True ∧ p5) → (p1 → (p4 ∨ (p1 → (False ∨ p5))))) ∨ (p5 ∨ (p2 → False)))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680208905192261981685065017234 : (((((False → (((p1 → ((p5 ∧ ((p5 → False) ∧ (p1 → p1))) ∨ p4)) ∨ False) ∨ p3)) ∨ (p1 ∧ p4)) → (p4 ∨ (False ∧ (p3 → p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319283881005565492970634272134 : (p4 ∨ ((True ∧ (((False → (((p4 ∨ p1) ∨ (p1 ∨ p1)) → (p2 ∨ False))) → p4) ∨ True)) ∨ (p2 ∧ (False → ((p1 ∨ p2) → (p5 → p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67926505306815231063783535372 : ((p2 → (((True ∧ ((p5 → (p3 ∧ p1)) ∨ True)) ∨ (False ∧ p2)) → (((p4 → p5) ∨ (p4 ∨ (False ∧ (True → p4)))) ∨ (False → True)))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Implications on the right can always be decomposed.
      intro h7
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193589293864417957937794244288 : (((False → p3) → ((False ∧ p2) → ((p3 ∧ p1) ∧ p1))) → ((((p4 → (True → ((True ∨ p5) ∧ p5))) ∧ (p3 ∧ True)) ∨ True) ∨ (p3 → False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62905354898519518790612525752 : ((p4 ∧ ((True ∨ p1) → ((((((p1 ∧ False) ∨ (True ∨ p2)) ∨ (True ∨ ((False ∨ p2) → (p5 → p1)))) → p2) → (p3 → p1)) ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204307586757925924096071706705 : (((False ∧ (p2 ∧ (False ∧ p2))) ∧ False) ∨ ((False → True) → (((False → ((p2 → p4) → (p3 → (p4 → True)))) ∧ p1) → (p2 ∨ (p5 ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116560571871489374046769721751 : (((p2 ∨ True) ∧ (p4 ∨ (((p1 ∨ ((p2 ∧ (p3 ∧ (p5 ∧ (p4 ∨ (p3 → p2))))) ∧ False)) ∧ (p5 ∨ (False → p1))) ∨ True))) ∨ (p2 → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216948293888396044116729198975 : (((p1 → (p1 ∧ False)) ∧ p1) → (True ∧ (True ∧ (p4 ∧ (((((p4 ∧ p4) → False) ∨ p1) ∧ ((p5 ∨ p4) → False)) ∨ ((p1 ∨ p4) ∧ p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h9 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h10 := h7 h9
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39596825153300098021633330182 : (((p2 ∨ (((((p5 → p2) → (True ∨ ((p4 ∨ (False → ((p3 → p1) → ((p3 ∧ p1) ∧ True)))) → p1))) → False) → p5) → False)) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614414259570651588023152924880 : (((((False → (((p3 ∧ p3) ∨ (((p4 ∨ False) ∨ (p2 ∧ p1)) ∧ True)) → ((p4 ∧ True) ∨ (p2 → p1)))) → ((True ∧ p1) ∨ False)) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_109984420222685153012695598033 : ((True → (p4 → ((((p5 ∨ p5) ∨ False) ∧ ((p3 ∧ True) ∨ (((p2 ∧ p5) → (False ∧ p3)) ∨ ((p3 ∨ p2) ∧ p3)))) ∨ True))) ∧ (p3 → p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184294549229363827689079395499 : (((((p2 → p2) ∨ True) ∧ ((p1 ∨ p2) ∨ (p2 ∨ False))) → p1) ∨ ((p4 → (p2 → ((((True → True) ∧ True) → (p1 ∨ p1)) → False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_127541278935443589311469254727 : ((p4 ∨ ((p2 → (((p1 ∧ ((True → p1) ∨ ((p4 ∧ True) → p3))) ∨ p4) ∨ p1)) ∨ ((p5 ∨ ((False ∨ p3) → p1)) → p2))) → (p3 ∨ True)) := by
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
theorem thm_5_vars_326437700524303422885871672303 : (True → ((((((p3 ∨ (False ∨ (((p5 ∧ True) → (((p1 ∨ True) ∨ True) → False)) ∧ (False ∧ (p4 ∧ p5))))) ∧ p1) ∨ p1) ∨ p2) ∨ True) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356759901631305623031839939890 : (p5 → (((((p4 → p4) → p2) ∨ p2) → p3) → (((p3 → (((((p1 ∨ False) ∧ False) ∨ (True ∨ p4)) ∧ p4) → False)) → (p1 ∨ p2)) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682918510583522360565853502865 : (((((p5 → False) ∧ (((p2 ∨ p1) ∨ (p5 ∨ p2)) ∨ (False ∧ (p3 → ((p5 ∧ p4) ∨ p1))))) ∧ ((p5 → p5) ∧ (p3 → (p4 ∨ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118755780921429265936692446423 : ((p5 ∨ ((p3 ∨ p1) ∧ (((True ∧ (p3 → p2)) → (p5 → (((p5 ∨ ((p2 ∧ (p1 ∧ True)) ∧ True)) ∨ True) ∧ p4))) ∨ p4))) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347567516823627651227180431050 : (p3 → (((False ∨ True) → (p4 ∨ True)) ∧ (((False → False) ∧ (p5 ∨ ((p4 ∨ (p4 ∧ ((p1 ∧ (p5 ∧ (p2 ∨ p5))) → False))) ∨ p1))) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257612534958351913623308310943 : ((p3 ∨ p2) → ((False ∧ ((p5 ∧ p3) ∧ (((p1 → (p1 ∨ ((True ∧ p3) ∨ p2))) ∧ ((True → p4) ∨ (p1 ∨ (False ∧ False)))) ∨ False))) ∨ True)) := by
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
theorem thm_5_vars_64051572557656614461614627467 : ((False ∨ ((((((False → p4) ∨ True) → ((p4 → p2) ∧ (p2 → (True ∧ (p4 ∨ p2))))) ∧ p4) → p5) ∧ ((p4 ∧ (p4 ∨ p5)) ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66384165729854361284828777474 : ((p5 ∨ (p4 ∨ ((p2 ∨ (p2 ∧ (p5 → p3))) ∨ (((p2 ∨ ((p5 ∧ p4) ∨ p5)) ∨ (p1 ∨ False)) ∧ ((p4 ∨ (True ∧ p1)) → p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118413704882005298590360416314 : ((p2 ∨ (p1 ∧ (p3 ∨ ((p2 → (((True → p3) ∧ p3) ∨ (((p2 → (True ∨ p3)) ∨ ((False ∧ True) ∨ p5)) ∧ p4))) ∧ True)))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_605366225773164291491048765016 : ((((p3 → ((((p4 ∧ p4) ∨ ((((((p5 → (False ∨ p3)) ∧ p1) ∧ p1) → (p5 → True)) ∨ False) → p1)) ∧ p2) ∧ (p3 → p2))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_781441101840358110376252599278 : (((p2 ∨ (p4 ∧ (((p4 ∨ ((p2 → p1) ∧ (p2 ∨ (((p1 ∧ p1) ∧ (p3 ∧ True)) ∨ (p5 ∧ True))))) ∧ False) ∧ (p2 → (False ∧ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192818833618671913090587711814 : (((p3 → (((False ∨ (p2 ∧ p4)) ∨ p2) ∧ p2)) → True) → ((((p2 ∨ p1) → False) ∧ ((p3 ∧ (p3 → p2)) ∨ p1)) ∨ ((p1 → p1) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258736951307577984644622112327 : ((True → True) → ((p3 ∧ p5) ∨ ((((True ∧ (p1 → p1)) ∨ p2) → ((p4 ∨ ((p5 ∨ (p3 ∧ p5)) ∨ (p1 → False))) ∨ (p1 ∨ p2))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215446179472773920223178465892 : ((p3 ∧ ((p2 → True) → p2)) ∨ (((((p3 → (p4 ∧ p3)) → p2) ∧ (True ∨ p5)) ∧ False) ∨ ((p5 → (((False ∧ True) ∧ p5) → p2)) ∨ p2))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_625672838224747556093369963213 : ((((p1 → ((((((p5 ∨ p1) ∨ (False ∧ p4)) ∨ p1) → (p2 ∧ p4)) → (p2 ∧ (p1 ∧ (p4 ∧ p5)))) ∨ (p2 ∧ (False ∨ p4)))) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225726003595309701388823492346 : (((p4 → False) ∧ p1) ∨ ((p2 ∨ ((True → ((((((p5 ∧ False) ∧ (True ∧ p2)) ∨ p4) → p1) → p4) ∧ p5)) ∨ (p1 → True))) ∧ (p2 → p2))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135049123179356800223141837187 : ((((((p2 ∧ True) ∨ p4) ∧ ((True → (p4 ∨ True)) ∧ ((True → (p2 ∧ (p2 ∧ p3))) ∨ p3))) ∨ True) ∨ (p3 → p5)) ∨ (False ∧ (p4 → p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258765108647486518958589641207 : ((True → False) → ((((p2 ∨ (p4 ∧ (p3 ∧ (p2 ∧ p5)))) ∧ False) ∧ ((p2 ∨ p5) → (((False ∨ p4) ∨ p2) ∧ (False → (p1 ∧ True))))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350138909276204606509420735147 : (p4 → (((((p3 ∨ ((p3 ∨ p2) ∧ (p3 → True))) ∧ (p3 → p4)) → p1) ∧ (p4 ∨ (p1 → (p3 ∨ (p4 → (p2 ∨ (True ∧ p5))))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64752390083685314167194188697 : ((p2 ∨ ((((p4 → p3) → ((p2 ∨ True) → p4)) ∧ (((p3 ∧ ((p5 ∨ (p4 ∨ ((False → False) ∧ False))) ∨ p1)) → p3) ∧ False)) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783972003573153441230061752763 : (((p3 ∨ ((p3 → (True → False)) → (p1 ∨ (p3 ∨ (p3 → ((True ∨ True) → ((p4 ∧ ((False → False) ∨ p5)) ∨ (p4 → (p1 ∨ p2))))))))) ∨ p4) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h5 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h6 := h1 h5
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h8 := h6 h7
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h10 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h11 := h1 h10
    -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
    have h12 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h11, we can now drive its conclusion.
    let h13 := h11 h12
    -- False on the left can always be used.
    apply False.elim h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65063688518849211064233950093 : ((p2 ∨ (p3 ∧ ((p3 ∨ (p5 ∨ ((p5 ∨ p5) ∨ p3))) ∨ (p3 ∨ ((p1 ∨ (p4 → (p4 → (p5 ∨ (p5 ∨ False))))) → (p2 → p1)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_21406995035638464505354567438 : (((((p1 → (((p5 ∨ p2) → True) ∨ p2)) ∧ False) ∨ p2) ∨ ((((p1 ∧ (p2 ∧ (False ∨ False))) ∨ p2) ∧ p5) ∨ (False → (p3 → p2)))) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67907302380557740925767747149 : ((p2 → (((((p5 → ((False ∨ False) → (True → False))) ∨ p3) ∨ (True ∧ p3)) ∧ p1) → ((((p3 ∧ p2) ∨ p5) → (p5 ∧ True)) ∨ p2))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228921581271479973913797486568 : ((p4 ∨ (p1 ∨ p3)) ∨ ((True ∧ ((p2 ∧ (((p3 → p2) ∨ (p2 ∨ (p3 → p5))) ∧ (True ∨ p2))) ∨ ((p2 ∧ p2) ∨ False))) → (p1 ∨ p2))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h11
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h13
        case inr h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h15
      case inr h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h17 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h5
        case inr h18 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h18
  case inr h19 =>
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h22
    case inr h23 =>
      -- False on the left can always be used.
      apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42702837586941221793948151426 : (((p5 ∨ ((((p3 → p1) → p2) ∨ (p1 ∧ (p3 ∧ p2))) ∧ (True ∧ ((p5 → (False ∨ (p2 ∧ (p5 → (p3 → False))))) → p1)))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_397175043601870783260489311169 : ((((p1 ∨ ((((p5 → (p1 ∨ (p4 ∧ p4))) ∧ p2) ∨ (((p4 → p2) ∨ ((False ∨ p5) ∧ (p2 ∧ (p4 → p1)))) ∧ True)) → p1)) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_342654351543664346572161421496 : (p2 → (((p3 ∧ ((((p1 ∨ False) ∧ True) ∧ p5) ∨ p1)) ∨ p3) ∨ (((((p2 ∧ (False ∧ (p1 ∧ False))) → (False ∨ p5)) ∨ False) ∨ p5) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206392554761672612134529466207 : ((p3 ∨ ((p3 ∨ (p5 ∧ p1)) ∨ p1)) ∨ (p1 → ((p4 ∨ (((p2 ∨ (p1 → p4)) → False) → ((True ∨ ((p4 → False) ∨ p4)) ∨ p3))) ∧ True))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607129004354023670326063767406 : ((((((p2 ∧ (((True ∨ p2) ∨ (p1 ∧ p5)) → p2)) ∨ ((p2 ∧ (p4 ∧ p3)) → (p3 → (p1 ∧ (p5 ∧ (p3 → p1)))))) ∧ p3) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42421127454069341541685715472 : (((p5 ∧ ((p5 → (((True → (p3 → p3)) → ((p4 ∨ ((True → (p2 ∧ False)) ∧ True)) → (p3 → p2))) ∨ p4)) → (p4 ∧ p1))) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47177063922651378511109078093 : ((((((p2 ∨ (p2 ∨ True)) ∧ (p5 ∨ (((p3 → False) → p5) → False))) ∨ p5) → ((p2 → (p1 → (p4 → p4))) ∧ p4)) ∨ (p1 ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_799941539041355102428507229290 : (((p2 → ((((p5 ∨ ((p1 → (False ∧ (((False → (((p4 → p3) → p4) → p5)) ∧ (p5 ∧ p1)) ∨ p1))) → p3)) ∨ p2) ∨ True) ∧ p2)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301858997936313800810666594804 : (False ∨ ((p1 → False) ∨ (False ∨ (((p2 ∧ ((p5 ∨ (p1 ∧ p2)) ∨ ((p1 ∨ (p3 ∨ p4)) ∨ (((p2 ∧ p5) ∧ p3) → p2)))) ∨ True) ∨ p5)))) := by
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
theorem thm_5_vars_105775302134311830517308727165 : (((((((p4 → ((p3 ∨ (p1 → True)) ∨ (p5 ∨ False))) ∧ p4) → p2) ∨ True) ∨ False) → (((p2 → (p3 ∨ p1)) ∧ False) ∨ True)) ∧ (True ∨ p4)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248303402562335130421435843984 : ((p2 ∨ p2) ∨ (p3 ∨ ((((p4 → p4) ∧ (p1 → ((p4 → p3) → p3))) ∧ (True → ((p5 ∧ p5) ∧ p5))) ∨ (False → ((p5 → p2) ∨ p3))))) := by
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
theorem thm_5_vars_658739301878109436164198847143 : ((((p5 ∨ ((((False ∧ ((p4 ∨ True) → p2)) ∧ ((((False ∧ (p5 ∨ False)) → True) ∧ p1) ∨ (p4 ∧ p4))) ∨ p3) ∨ p3)) ∨ (True ∨ p2)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_45311393616413235698421511372 : (((p3 ∧ (((((((((p1 ∨ False) → p5) ∧ p4) ∧ True) ∨ ((p1 → (False → p5)) ∨ p1)) → (True ∧ p4)) ∧ p4) ∧ p4) → p3)) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65379256815911718543295429165 : ((p3 ∨ (((False → (p1 ∨ p4)) ∧ (p1 ∧ (False ∨ p2))) ∧ (((((True ∧ p3) → ((False ∨ p3) ∨ False)) ∨ (False → True)) → p3) → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204631234595459246597153124326 : (((False ∧ ((p2 ∧ p2) ∧ p1)) ∨ p4) ∨ (True ∨ (((p3 ∧ (p1 ∧ (True ∨ p4))) → (p4 → (False → p4))) → ((True → (True ∧ p2)) ∧ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_791478848132482722863284138120 : (((True → ((p4 ∧ ((p4 ∨ p1) → (((((((True ∧ p1) → p5) → (p3 ∨ False)) ∧ p3) ∧ p4) ∧ (p1 ∧ (p1 ∧ p4))) ∨ p2))) ∨ True)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_779519618985358761995422546637 : (((p2 ∨ (((p2 ∧ (p3 ∨ (p3 → p2))) → (((p2 ∨ (p3 ∨ p4)) → (((True → (p5 → p4)) → (p4 ∧ p5)) → False)) → p3)) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114652301903970039302585389329 : ((((True ∧ ((True ∧ (p2 ∧ (False ∨ True))) ∨ p1)) ∧ ((True → (p3 ∨ p3)) ∧ False)) ∨ ((((p1 ∧ p1) ∧ p4) → p5) → p5)) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684096617529443895692498480933 : (((((((p1 ∨ ((False ∨ p3) ∨ (((p2 ∨ p2) ∨ p4) ∧ p4))) → p5) → False) ∧ (p3 ∨ p2)) ∨ ((p3 ∨ True) ∧ ((p4 → p2) ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615293555342350681023693137980 : ((((((((p1 ∧ ((False ∧ False) → p4)) ∨ p1) ∨ ((p2 ∧ True) ∧ (p5 ∧ p3))) ∨ False) ∨ ((p3 ∧ p1) ∨ (p1 → (p4 → p1)))) ∨ p4) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61514904435682233088211082718 : ((p1 ∧ (((((p1 → p3) ∧ (p4 ∨ (p5 → (p4 ∨ True)))) ∧ p3) → (p2 ∨ (p3 → p1))) ∧ ((True → (p2 ∧ True)) ∨ (False ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167434478040712415546359803051 : (((True ∨ ((p1 → p2) ∨ (((p1 ∨ ((p5 ∨ p2) ∧ False)) ∧ p4) → (False ∧ p5)))) → p3) → ((((p2 ∨ (p2 ∨ False)) → p1) ∧ False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_725830971924634653368567456964 : (((((p5 ∨ p2) ∧ p1) ∨ (((p3 → (True ∨ False)) ∧ (p4 → False)) ∨ ((p3 ∧ (((True → (True → p1)) → True) ∨ (p3 ∨ p3))) ∨ True))) ∨ p1) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41466962168282963195012646178 : ((((p4 → ((True → (p2 ∧ (True → (p2 → (p3 ∨ True))))) ∧ False)) ∧ (p4 ∧ ((((p1 ∨ p3) ∨ (p4 ∨ p5)) → p1) ∨ p5))) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57113986495899125154439344862 : ((((p2 ∨ p4) ∧ p1) ∨ (p2 → (p1 ∧ ((p3 ∨ (((p3 ∨ (((p1 → p1) → True) ∨ p1)) ∧ p3) → (p2 → (p4 → p1)))) ∧ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191238740807040344293346281221 : (((p5 → (False → p2)) → (((p2 ∧ p1) ∨ p5) ∧ p4)) ∨ (((p1 ∨ True) ∨ p2) ∨ (p4 → ((p5 ∧ p1) ∨ (((p5 ∧ False) → p1) ∧ p4))))) := by
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
theorem thm_5_vars_669334196547351086483876360489 : (((((((((p2 ∧ True) → p1) ∧ p3) → True) ∧ (p4 ∧ (((False ∨ p4) ∧ (p5 ∨ p2)) ∨ p5))) ∧ (p5 ∨ p2)) ∨ (True → (True → True))) ∨ p1) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_587129424356369608880089579040 : (((((p2 → (True ∧ (((p3 → (True ∧ (p2 ∧ True))) ∧ (False ∨ p3)) → ((True ∨ ((p4 ∨ (p4 → p3)) ∨ p3)) → p5)))) ∧ p1) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301398188550965021444468929459 : (False ∨ ((True → ((p5 ∧ p4) ∧ p5)) ∨ (True → ((((p3 ∧ ((True ∨ p2) ∧ p4)) ∨ (False ∨ (p4 ∨ (False ∧ p2)))) ∧ p2) ∨ (p4 ∨ True))))) := by
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
theorem thm_5_vars_328126720481620756020133485917 : (True → (((p4 → (p2 ∨ ((p4 ∧ False) ∨ p5))) → (((True ∨ p2) → (((p5 ∨ p2) ∧ p1) ∧ (False ∨ p4))) → p4)) ∨ (p3 → (False ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (True ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322583401365766437504052656442 : (p5 ∨ ((True → ((((True ∨ (p1 → (p5 ∨ p1))) ∧ (p5 → (p4 ∨ p2))) ∨ ((((p2 → p2) ∨ p1) ∨ p2) → (False → p1))) → p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46824766816324334572905827107 : ((((((p1 ∧ (p3 ∨ ((p4 ∨ False) → p3))) → ((p1 → p2) ∧ ((p1 ∧ True) → (True → p3)))) ∨ (p5 → True)) ∧ p2) ∨ (False → p5)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_441426869068001676428991291345 : ((((p3 ∨ (((((((p3 → (p1 → (p2 ∧ p1))) ∧ p1) → False) ∨ p1) ∨ p4) → p2) → ((p5 → p3) ∨ True))) ∧ (p3 ∨ (True ∨ False))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314256753503714604559003917160 : (p3 ∨ (((p1 ∧ ((p4 ∧ (p2 ∧ False)) → True)) ∨ (((p2 ∨ ((True ∨ True) → (p3 ∨ p4))) ∨ (p1 ∨ True)) ∨ p5)) ∨ (p3 → (False ∧ p4)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299237947064968481429208152881 : (False ∨ (((True → (((p1 ∧ p2) → (p3 ∨ p5)) ∨ (((True ∧ True) ∨ False) → ((p1 ∨ True) ∧ (True → p1))))) ∧ (p3 ∨ (True ∨ p1))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



