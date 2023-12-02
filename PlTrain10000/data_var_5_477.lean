variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164347149868643093171586959304 : ((p3 → ((((((p3 → p4) ∧ p5) ∨ (p2 ∧ p2)) → (False → (False ∨ p4))) → p1) ∨ p3)) ∧ (False → (p2 → (p5 ∧ ((p4 ∧ True) → True))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_189725754147945611865382847444 : ((p4 ∨ (((False ∨ (p3 ∨ p1)) ∧ p2) ∨ (p2 → True))) ∧ (((p4 → p5) → ((p5 → (False ∧ p2)) → True)) ∨ (p5 → ((p5 ∧ True) ∨ p3)))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307435431086678308074185078445 : (p1 ∨ (p5 ∨ ((((p4 → (p2 → p1)) ∨ (((p4 → (True → p1)) ∧ True) ∧ p4)) ∨ ((p2 ∧ (p2 ∨ p4)) → (p3 → True))) ∨ (True → p2)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347516340248072104707295510897 : (p3 → (((False ∨ (p5 ∨ (p1 ∨ False))) → p5) → (p4 → (p5 ∨ ((((p1 → p4) ∧ (p5 ∨ p2)) ∨ (((p1 → p1) → p2) ∧ p5)) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165910245491380077993219314897 : (((p2 → (p4 → p2)) → ((p5 → (p1 ∨ p4)) ∧ (p2 → ((p1 → p2) → (p5 → False))))) ∨ ((p1 ∨ True) ∨ (p4 ∨ (True ∨ (p4 → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149532715480707550422305160153 : ((p2 ∧ ((((p3 → (False ∨ p2)) ∨ ((((p5 → p1) ∧ p3) → p5) ∧ (p2 → (p2 ∧ False)))) → p2) ∧ p2)) ∨ (p4 → (p5 ∨ (p2 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51238119116754844358762057513 : ((((p3 ∨ (p4 ∧ p1)) ∧ ((p1 ∨ ((False → p1) ∨ (p5 ∧ (p2 ∧ True)))) ∧ (p4 ∧ p4))) ∨ ((((p3 → True) ∧ p3) → p2) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_962997027489404962381150156921 : ((((p1 → p1) ∧ ((((True ∧ ((p1 → True) → p1)) ∨ False) ∨ (((p3 ∧ p3) → (p1 → (p5 → p3))) ∨ p2)) → ((p1 ∧ p5) ∧ False))) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (((True ∧ ((p1 → True) → p1)) ∨ False) ∨ (((p3 ∧ p3) → (p1 → (p5 → p3))) ∨ p2)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h5.left
    let h9 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h10 := h3 h4
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- False on the left can always be used.
  apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42155698836180694793805805980 : ((((p1 → p5) → ((p1 ∧ ((True → (p2 ∧ (p4 → (p3 ∨ (p4 → (True ∧ p2)))))) ∧ ((p4 → (p2 → p1)) ∨ p4))) ∨ p2)) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41418669025481547421150083758 : ((((p2 ∧ ((False ∨ (((p4 → (p1 → False)) ∨ p1) → True)) → (p3 → p4))) ∨ ((((p1 ∧ p5) → p2) ∧ (p4 → p3)) ∧ p4)) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66514904478369632491477861919 : ((True → ((((True → (False ∨ (((p1 ∧ (p1 ∨ p4)) ∧ ((True → p2) ∧ p2)) ∧ (p4 → ((p1 ∧ p1) ∧ p4))))) → p2) ∨ p3) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66442960989335720320859839266 : ((True → ((((True ∧ (((((p3 → (False ∧ p4)) ∧ p5) → p5) → p2) → p3)) ∧ (p2 ∨ (False ∧ (p3 ∨ p2)))) ∧ (p1 → p2)) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180411530798204595859952918516 : (((p4 → (True ∨ (((p2 ∨ p4) ∨ p2) → (p2 ∧ False)))) ∨ (p4 → p3)) → ((((p2 → (p2 ∧ False)) → p4) ∧ (p3 → (p5 ∨ p5))) ∨ True)) := by
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
theorem thm_5_vars_4012634774625055739503729041 : (p1 ∨ (p1 → ((((p3 ∧ p3) ∨ (((p5 → p3) ∨ p4) ∨ (p5 ∨ (p1 ∨ ((p4 → p2) ∨ ((p3 ∧ p4) ∨ p3)))))) ∨ p4) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_753787384412094628388288807346 : (((False ∧ ((((((p2 ∧ False) ∧ p2) ∨ (p3 ∨ p5)) ∨ p4) ∧ p3) ∧ ((p5 ∧ ((p4 → (False ∨ p4)) ∨ ((True ∧ p1) ∨ p2))) ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50887571818689041795074492791 : ((((((False → p1) ∧ p3) ∧ ((((True ∧ p3) ∨ p2) → (p1 → p4)) → (p2 ∨ p1))) → True) ∧ ((p5 ∨ (p3 → p3)) → (p4 → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175474435975708102877500756991 : ((p2 → ((p4 → (p5 ∧ p3)) ∨ (p5 ∨ (p2 ∨ ((True → (p1 ∨ p5)) → p5))))) → (((((p5 ∨ p4) ∨ False) ∨ p1) ∧ (p5 → p4)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209462341892839256798728305607 : ((p3 → (((True ∨ True) ∧ p3) ∨ p2)) → ((((p3 ∧ False) ∨ (True → ((False ∨ ((True ∧ False) → p2)) ∨ p2))) → False) → (p5 → (False ∧ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p3 ∧ False) ∨ (True → ((False ∨ ((True ∧ False) → p2)) ∨ p2))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- False on the left can always be used.
    apply False.elim h8
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h4
  -- False on the left can always be used.
  apply False.elim h9
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h10 : ((p3 ∧ False) ∨ (True → ((False ∨ ((True ∧ False) → p2)) ∨ p2))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- False on the left can always be used.
    apply False.elim h14
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h15 := h2 h10
  -- False on the left can always be used.
  apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190400265825540633821134092474 : (((p3 ∧ (((p1 ∨ p5) ∨ p1) ∨ (p2 ∧ p3))) ∨ p4) ∨ (False ∨ (True ∨ ((p1 ∨ (p5 ∧ (p3 ∨ ((p5 ∧ p4) → p4)))) ∧ (p1 ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42965756772777310126650308145 : (((p5 → (((p4 → (p2 ∧ (((p3 → (((p4 ∧ (False ∨ False)) ∨ p3) ∨ p5)) ∧ True) ∧ ((p3 → p2) ∨ p1)))) ∧ p5) → p1)) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198367637620032029728838964202 : ((p3 ∧ ((False ∨ ((p5 → p2) → p5)) ∧ True)) ∨ (p2 → ((False ∨ ((p1 ∧ p1) ∨ p2)) ∨ ((p5 → ((p4 ∧ p5) ∨ p4)) ∨ (p2 → False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658594549808261625143352924226 : ((((p3 ∨ ((((p1 ∨ p3) → ((p4 → ((False ∧ False) → p4)) ∨ p3)) ∧ ((p5 ∧ p1) ∧ ((p4 ∨ True) → p5))) → p4)) ∨ (True ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62183082207492104244219911840 : ((p3 ∧ (((True ∧ (((p4 ∨ (p3 ∧ p4)) ∨ (p1 ∧ False)) → ((True ∧ ((p5 ∨ (True ∧ (p2 ∨ p2))) ∨ False)) → p1))) ∧ p2) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113576642822270529604218163301 : (((False ∧ (((((False ∨ p5) ∨ (p3 → ((True → p2) ∧ ((p5 ∨ p2) ∧ True)))) ∧ p5) → (p5 → p3)) ∨ False)) ∨ (True ∨ False)) ∨ (p4 → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_700599045800513964184941242417 : ((((p1 → ((p2 → (((False → (True ∧ p3)) → False) ∨ True)) ∨ p1)) → ((p2 → p3) ∧ ((True → p2) → ((p2 ∨ (False ∨ True)) ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148654873902260754464841289085 : ((((True ∧ p4) ∨ ((True → (p3 → True)) ∧ p2)) ∧ (p3 → (p1 ∨ (p4 ∨ (p2 ∨ (p2 ∨ (p2 ∧ p4))))))) ∨ ((False ∧ (False ∧ p3)) → p4)) := by
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
theorem thm_5_vars_112441001235678210231110310933 : (((((((((p5 ∨ False) ∧ (p2 ∨ (((False → False) ∧ p3) → True))) ∨ False) ∨ ((p4 ∨ False) ∨ p1)) ∧ p3) → p3) ∨ p1) → p5) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51529754024450404192002928275 : ((((True → p4) → (((False ∨ (p1 → (p1 ∨ ((True ∧ p3) ∨ (p5 ∧ p5))))) → p2) ∧ p5)) → (p4 ∨ (p3 ∨ ((False ∨ True) → p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244554034590999986185666749454 : ((False ∧ p4) ∨ (((True → ((p2 ∧ (((p4 ∨ True) ∧ (True ∨ (p5 ∧ p4))) → p3)) ∨ p5)) ∨ (((p5 ∧ p5) ∨ p2) ∨ (p4 ∨ True))) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66252192383264713889627865567 : ((p5 ∨ ((True → ((False → p4) ∨ p2)) ∧ ((p1 ∧ ((p3 → (p4 ∧ p2)) ∨ ((p4 ∧ (True → False)) → (p2 ∧ p3)))) ∨ (True ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180875579677447143356415839942 : (((p4 → (p3 → False)) ∨ (False → (((False ∨ p4) → (p4 → p2)) ∨ False))) → (((True ∧ (True ∧ True)) → p3) ∨ ((p3 → (True ∨ p5)) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172574633846521645726655486980 : (((p3 → (p1 → p2)) ∨ (((False ∨ (p1 ∧ ((p1 ∨ p2) ∨ True))) ∧ p3) ∨ False)) ∨ (((p2 → p5) ∨ ((False ∨ p5) ∨ (True → p3))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_240032553093142737915550337980 : ((p4 ∨ True) ∧ ((p1 ∨ p2) ∨ (((((True ∧ True) ∨ p1) → False) → (False ∨ ((((p4 ∨ p3) → p3) ∨ (p4 ∧ p4)) → p3))) ∨ (False ∧ p1)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((True ∧ True) ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54036871253135766665399613663 : ((((((p4 ∨ p1) → (p3 → p3)) ∨ False) → (True ∧ p2)) → ((False ∨ ((p5 ∨ ((p2 ∨ (True ∨ True)) ∧ p3)) ∨ (p5 → p2))) ∧ p2)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (((p4 ∨ p1) → (p3 → p3)) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h3
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- One of the premise coincides with the conclusion.
  exact h9
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h10 : (((p4 ∨ p1) → (p3 → p3)) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h11
    -- Implications on the right can always be decomposed.
    intro h12
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h13 =>
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h14 =>
      -- One of the premise coincides with the conclusion.
      exact h12
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h15 := h1 h10
  -- We need to get the right conjuct of h15 based on <expert-advice>.
  let h16 := h15.right
  -- One of the premise coincides with the conclusion.
  exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_154146530007696952540919337541 : ((((((p4 → p5) → False) → (p1 ∨ ((p4 ∧ (p2 → ((p5 ∧ p4) → False))) ∨ True))) ∨ False) ∨ True) ∧ (((p5 → p4) → (p2 ∧ True)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48045919312722008592641459264 : (((((False ∧ ((False ∨ p1) ∨ p4)) ∨ (p3 → (p1 ∨ p5))) → (p5 → ((p3 ∧ p5) ∧ (p1 → ((p5 → p1) ∨ p2))))) → (False ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52385126438964313621847477621 : ((((((p5 ∨ False) → (p4 ∧ p4)) → p3) ∧ (False → (p5 ∧ (False → p3)))) ∧ (p5 → (((p1 ∨ ((p4 → p5) → p3)) ∨ p3) ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69353429773466897505934589311 : ((p5 → (p3 ∨ ((((((p3 ∨ (True ∨ p4)) ∨ ((p4 ∨ (p4 → False)) ∧ p2)) → p5) ∧ p5) → p3) → (p4 → ((p4 → False) ∨ p3))))) ∨ p5) := by
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
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((((p3 ∨ (True ∨ p4)) ∨ ((p4 ∨ (p4 → False)) ∧ p2)) → p5) ∧ p5) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- One of the premise coincides with the conclusion.
          exact h1
        case inr h10 =>
          -- One of the premise coincides with the conclusion.
          exact h1
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h14 =>
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h15 =>
        -- One of the premise coincides with the conclusion.
        exact h1
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h16 := h2 h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_162318460868083189680903570678 : (((((((False ∧ ((p1 ∨ p5) → False)) ∨ True) ∨ (p5 ∨ (p5 ∨ True))) → p1) ∧ False) ∨ True) ∧ ((p5 → p5) ∨ ((p5 ∧ (p1 ∨ p1)) ∨ True))) := by
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
theorem thm_5_vars_657529062037041208819545761517 : (((((True → p3) ∨ ((False ∨ (((p2 ∧ (p2 → p5)) ∨ p3) ∧ (True → (p2 ∨ (False ∨ (p3 → p1)))))) → (p3 ∨ p1))) ∨ (True ∨ True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_632615935924116586102696223797 : (((((p1 → ((p4 ∨ (p2 ∧ (((False ∧ (False ∨ p1)) ∨ p4) → False))) → (((p4 ∧ p3) → p3) ∨ (p5 ∧ (True → p1))))) → p2) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48043668835512823514009397443 : ((((((p1 → (False ∨ ((p2 → p2) → p3))) ∧ p3) ∨ p4) → (p3 ∧ (((False → (p4 ∨ (p3 → p4))) ∨ p4) ∧ False))) → (p2 → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49258894509905287836723165285 : (((False ∧ (p2 ∧ (((((((p1 → p3) ∨ False) ∧ ((False → (p1 ∧ True)) ∨ False)) ∨ p4) ∨ p2) ∧ p5) ∨ p1))) ∨ (False ∨ (True ∨ p2))) ∨ p3) := by
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
theorem thm_5_vars_43509569120221882677594132601 : ((((p2 ∨ ((((False ∨ p3) → False) → (((p2 ∧ p5) → (p3 ∨ ((p4 → False) ∧ p5))) ∨ p4)) → ((p3 ∨ p3) ∨ True))) ∨ p1) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712099107444433109772336439852 : (((((False ∨ (p3 → (False ∧ True))) ∨ p5) ∨ (p5 ∨ ((((p3 ∧ ((p1 ∨ ((p3 ∧ True) → p1)) → (p2 → True))) → False) ∧ p5) ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262374258753838812430035749444 : (True ∧ (((p5 ∧ p4) ∧ ((p1 ∨ ((False ∧ p5) → (p3 → False))) ∧ (p4 ∧ (((((p4 ∧ p1) → True) → True) → p4) → (False ∧ True))))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111865596446504473237523091947 : ((((p5 → ((((True ∧ ((p2 → (p5 ∧ p3)) → (False ∨ False))) ∧ p3) → p1) → p1)) ∧ ((p4 ∨ p2) ∨ (False → p3))) ∨ p4) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133519334828672753228703393343 : (((((((p4 ∧ p5) ∨ (((((p2 ∨ False) ∨ p2) ∨ p4) ∨ (p5 ∨ (p2 ∧ False))) ∧ p2)) → False) → p3) ∧ p5) ∧ p5) ∨ (p5 → (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134012834763079376870223589592 : ((((True → (p4 ∨ (((p5 ∨ ((p4 → p1) ∧ (p4 → (p3 ∧ p3)))) ∨ (False ∨ (False ∨ True))) → p5))) ∧ True) ∨ p2) ∨ ((p5 ∨ True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320093265894035101570193567959 : (p4 ∨ (((p4 ∨ p4) ∨ p2) → ((p1 ∨ (((p3 → p3) → ((p4 ∨ p3) ∧ ((p3 ∧ p4) ∨ p5))) ∧ p5)) ∨ ((p1 ∧ (True → p3)) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316450488491049891397736075727 : (p3 ∨ (p1 ∨ (((p4 ∨ p1) ∧ ((((p1 → False) ∧ p5) ∨ p4) ∨ p2)) ∨ (p3 → ((p2 ∧ ((True ∧ p4) ∧ ((p5 ∨ p4) ∨ p4))) → p2))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h11 =>
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h12 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312907616208727562423953315050 : (p3 ∨ ((p5 ∨ ((((p1 → p4) ∨ (p1 ∨ (p2 ∧ (p4 → ((p5 → p2) ∨ (p1 ∨ p3)))))) ∨ p3) ∨ ((True ∨ p5) ∨ (p4 ∧ True)))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_352248950265434009733979027625 : (p4 → ((p2 ∨ (p4 → (p1 ∧ p3))) ∨ (((p5 ∨ p5) ∨ (((p5 ∨ p2) ∧ ((p4 → p5) → (p1 → p4))) → False)) ∨ (False → (p4 ∨ False))))) := by
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
theorem thm_5_vars_110725347228345421378492750666 : (((((((((p1 ∧ p3) → p1) ∨ ((p2 ∧ ((True ∧ p2) → False)) → True)) → True) → p2) ∨ ((p3 ∨ p5) → True)) ∧ p4) ∧ p5) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257378316436952915885694052828 : ((p2 ∨ p5) → (((((((((((False ∧ True) → p3) → p4) ∨ p1) ∧ p5) → p4) ∨ (p2 ∧ p2)) → False) → (p4 ∧ p3)) ∧ False) ∨ (p4 → p4))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59588257559550483268089395937 : (((p4 → p1) ∨ ((((p2 → (p5 → p3)) → (p3 ∧ (p4 → ((p1 ∨ (p3 → p2)) ∧ p2)))) ∨ True) ∨ (((True ∧ p3) ∨ p2) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157902265527378955032713245450 : (((((p4 ∧ ((p1 ∨ False) → p4)) ∧ (p2 → p1)) → p3) → (((p3 ∧ p4) ∨ (p4 ∨ p4)) ∧ False)) ∨ (p3 → (True ∨ ((p1 ∨ p5) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215933817449179402732767779360 : ((p3 ∨ (True → (False ∨ p2))) ∨ ((True ∧ (True ∧ (p4 ∨ p3))) → (False ∨ (((p3 → (((p1 → (p1 ∨ True)) → p3) ∨ p1)) ∨ p3) ∨ True)))) := by
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
theorem thm_5_vars_17190645420254905005991237542 : (((((p4 ∨ p5) → (((True ∧ p3) → p1) → ((p4 ∧ (p3 ∨ (p4 ∨ p1))) ∧ p4))) ∧ (p3 ∨ (p4 ∨ p4))) → ((p2 ∨ p3) ∨ True)) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69572990226336805623015296986 : ((((((True ∨ True) → False) ∧ (((p3 → p3) ∨ (p1 → p5)) ∨ (((p3 → ((p1 ∨ True) ∧ p4)) ∨ p3) ∨ (p3 ∧ p4)))) ∧ p4) ∧ p3) → p2) := by
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
  cases h7
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h10 : (True ∨ True) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h11 := h6 h10
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h13 : (True ∨ True) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h14 := h6 h13
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h18 : (True ∨ True) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h19 := h6 h18
        -- False on the left can always be used.
        apply False.elim h19
      case inr h20 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h21 : (True ∨ True) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h22 := h6 h21
        -- False on the left can always be used.
        apply False.elim h22
    case inr h23 =>
      -- Conjunctions on the left can always be decomposed.
      let h24 := h23.left
      let h25 := h23.right
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h26 : (True ∨ True) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h27 := h6 h26
      -- False on the left can always be used.
      apply False.elim h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157051148363955822314266061733 : (((p2 ∧ (((((p2 → p2) ∨ p2) ∨ p3) ∧ (True → (p5 ∧ (p5 → p3)))) → (False ∧ False))) ∨ p5) ∨ ((True ∨ ((p3 → p5) ∨ p2)) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320498709670639349354781945984 : (p4 ∨ (True ∧ (((((((p2 ∨ (p5 → True)) ∨ p5) → False) ∨ p5) ∧ p4) ∨ (((((p4 → p1) ∨ (p5 ∧ p2)) ∨ True) ∧ p4) → True)) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_204653853328773061193906791601 : (((p3 ∧ (p5 ∧ (p5 ∨ p5))) ∨ False) ∨ (True → ((p1 ∨ ((p5 → (p2 → True)) ∨ (((True ∧ p2) ∨ ((p1 ∨ p5) ∧ p5)) ∨ p2))) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148667295030118241841976187816 : (((p5 → (((False → p4) ∧ p3) → (False ∧ p3))) ∧ (((p4 ∨ (p5 ∨ p3)) ∨ ((False ∧ True) → p5)) → p1)) ∨ (p4 → ((p4 ∨ p3) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245584119643452979945775455355 : ((p3 ∧ False) ∨ (((((p1 ∨ (((False ∨ p5) ∧ True) ∧ (p2 ∧ (True → p5)))) ∨ False) ∧ ((False → (p1 → (p2 ∧ p1))) ∧ p1)) ∧ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216474954092846507517108463891 : ((p5 → ((p2 ∧ p1) ∧ True)) ∨ ((((True ∨ True) → p5) ∧ p2) ∨ (((p5 ∨ p3) → ((False ∧ ((p3 ∨ p1) ∧ (p2 → p1))) ∧ p4)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702797360598112499244525874811 : ((((((p2 ∨ (p3 ∨ p4)) ∧ p3) ∧ ((p5 ∧ p4) ∧ True)) ∨ ((True ∨ p3) ∧ (((True ∨ (p2 ∨ p4)) → p3) → ((p2 → p4) ∨ p3)))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ (p2 ∨ p4)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168583495007456506710323740815 : ((p2 ∧ ((p3 ∨ (p2 ∧ (False ∧ p4))) ∨ ((p5 ∧ p2) ∧ (True → ((p4 ∧ p1) ∨ p5))))) → (((p4 ∧ (p3 ∨ p1)) ∧ p4) ∨ (True ∨ False))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- False on the left can always be used.
      apply False.elim h9
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h12.left
    let h15 := h12.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246617274416930209837505676355 : ((p5 ∧ p3) ∨ (((p3 ∨ (p1 ∧ (p5 → ((True → ((p5 ∨ p2) → (False ∧ ((p3 ∨ ((True ∨ True) → p3)) → p2)))) ∧ p5)))) ∨ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261552988173477008453834981627 : ((p5 → p4) → ((((p3 ∨ False) → (((False ∧ p5) ∧ (False ∧ p4)) ∧ True)) ∨ (p3 → (p3 ∨ ((p4 ∧ (p4 ∨ (p3 ∨ p1))) ∧ p5)))) ∧ True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137398317921610070095036936579 : ((p3 ∧ (p5 ∧ ((p2 ∨ ((True → (((False ∧ (p2 ∧ False)) ∨ (p5 ∨ True)) ∧ (p5 ∨ (p4 ∨ p3)))) → False)) ∨ p4))) ∨ (p2 → (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133712548065345848248201269897 : ((((((True ∧ p5) ∨ (p4 ∧ ((p3 ∨ p5) → p1))) ∧ ((False → False) → p4)) → (p5 ∨ (p5 ∧ (False ∨ p5)))) ∧ p4) ∨ (False → (True ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137276373881281975009768564420 : ((p1 ∧ (p2 → (p2 ∧ ((p1 ∧ p1) ∧ ((p3 → (((p3 ∧ p2) ∨ p3) ∧ p2)) ∧ (p3 ∧ ((p1 ∨ True) ∧ p2))))))) ∨ (p5 ∨ (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190023248357276064981207834033 : ((((p2 ∧ (((p1 ∧ p1) → False) ∨ p1)) ∧ p4) ∧ False) ∨ (p5 ∨ (p2 → (p4 → (((p1 ∨ (p3 ∨ ((True ∧ p5) ∨ p3))) ∨ False) ∨ p2))))) := by
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
theorem thm_5_vars_870771548648814118136601601047 : ((((False ∨ ((p4 ∨ ((p4 ∨ (((((((((p1 ∧ p5) ∧ True) ∨ True) ∧ p1) ∧ p5) → p1) ∨ p2) → p2) ∨ p4)) ∨ False)) ∨ True)) → False) → False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False ∨ ((p4 ∨ ((p4 ∨ (((((((((p1 ∧ p5) ∧ True) ∨ True) ∧ p1) ∧ p5) → p1) ∨ p2) → p2) ∨ p4)) ∨ False)) ∨ True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56882759196581946416036788113 : (((p2 ∧ (p4 ∨ p4)) ∧ (p5 ∨ (((p4 ∨ (((((p2 ∧ False) ∧ True) ∨ (p5 ∨ p5)) ∧ p1) ∧ True)) → (p2 → (p2 → p1))) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45763201962869193747163137597 : (((False → ((p4 → p2) ∧ ((False ∨ (((p5 ∧ p5) ∨ p3) → (p3 ∧ (((False ∧ (p2 ∨ p2)) ∧ (True → False)) ∧ p1)))) ∨ False))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_647004474323733591242586548 : ((((((p4 ∧ p2) ∨ ((p1 ∧ p2) ∨ (p2 ∧ p4))) → True) → (True ∧ ((p3 → p1) ∨ (True ∨ p3)))) ∨ (p3 ∨ (p2 ∨ True))) ∨ p5) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135987454569462346411212292366 : ((((p1 ∧ ((p3 ∧ p2) → p2)) ∧ ((True ∨ p5) → True)) ∨ (((True ∧ p2) ∧ (False ∨ (p1 ∨ (p2 ∧ p5)))) ∧ False)) ∨ ((False ∧ p5) → p4)) := by
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
theorem thm_5_vars_198046088321869331409836091947 : (((p3 ∧ True) ∨ (p3 ∧ ((p5 → p4) ∧ p2))) ∨ ((((False → ((True ∧ True) → (p3 ∨ p2))) → (p1 ∨ p3)) → (False ∨ False)) ∨ (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153397344338792969155394356378 : ((p3 ∨ (((False → (p5 ∧ ((p2 ∨ p3) ∨ (False ∧ True)))) ∨ (p3 → p2)) ∨ (((p1 → p4) → p4) ∨ p4))) → (((p3 → p3) → p3) → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h7 : (p3 → p3) := by
          -- Implications on the right can always be decomposed.
          intro h8
          -- One of the premise coincides with the conclusion.
          exact h8
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h9 := h2 h7
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h10 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h11 : (p3 → p3) := by
          -- Implications on the right can always be decomposed.
          intro h12
          -- One of the premise coincides with the conclusion.
          exact h12
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h13 := h2 h11
        -- One of the premise coincides with the conclusion.
        exact h13
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h16 : (p3 → p3) := by
          -- Implications on the right can always be decomposed.
          intro h17
          -- One of the premise coincides with the conclusion.
          exact h17
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h18 := h2 h16
        -- One of the premise coincides with the conclusion.
        exact h18
      case inr h19 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h20 : (p3 → p3) := by
          -- Implications on the right can always be decomposed.
          intro h21
          -- One of the premise coincides with the conclusion.
          exact h21
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h22 := h2 h20
        -- One of the premise coincides with the conclusion.
        exact h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47616660887445791083912830141 : (((p5 → ((((False → True) ∧ (((p5 ∧ (False ∧ True)) ∧ False) → (((p5 → p2) ∨ (p2 → p4)) ∨ False))) → False) ∨ True)) ∨ (p4 ∧ p4)) ∨ False) := by
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
theorem thm_5_vars_48650394366694152745087954978 : (((((p5 ∨ ((p5 ∧ (p5 ∧ p5)) ∨ (p1 ∧ p4))) ∨ (p4 ∧ (p2 ∨ p2))) ∨ (True ∨ ((p3 ∨ False) ∨ True))) ∧ (p2 → (False ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238107308418852593787219459983 : ((True ∨ p2) ∧ (p4 → ((p3 ∨ (p1 ∨ (p4 → (((True ∧ p1) ∧ p3) → p5)))) ∨ (True ∧ ((((True ∨ (True ∨ p3)) → p2) ∨ p2) ∨ p4))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354100511594522066074882088468 : (p4 → (p5 → (((p2 → (p3 → (p3 ∧ ((p3 ∨ (p2 ∨ (p4 ∨ False))) ∨ p5)))) ∧ p4) → (((p1 → p3) ∧ p1) ∨ ((p1 → p4) ∨ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h6
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353519994434434863872564963435 : (p4 → (p2 ∨ (True → ((p1 ∨ ((((p3 ∨ False) ∧ True) ∨ (p3 ∨ p5)) ∧ (p3 ∨ (p1 ∧ (False → p3))))) ∨ (p2 ∨ (p1 ∨ (p3 → p3))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301248771509693600040999229553 : (False ∨ (((p4 ∨ ((False → p5) ∧ p5)) → p1) ∨ ((False ∨ ((p4 ∨ p4) ∨ True)) ∨ ((p4 → (p5 ∧ (((p1 ∨ p4) → p2) ∧ p1))) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_46530499922908148406866721037 : ((((p4 ∧ p2) ∨ (p5 ∨ ((p1 → p5) ∨ ((p1 ∧ (p5 ∨ False)) → (p2 ∧ (True → ((p5 → (p1 ∨ p2)) → False))))))) ∧ (True ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233232512852907093507782897802 : ((p5 ∧ (p5 → False)) → (p2 ∨ (((False ∨ p2) ∧ True) ∧ (((((p1 → p5) ∨ p3) ∨ p4) ∨ (p1 → ((False ∨ p4) → p1))) ∨ (p1 ∧ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66543140659489253213726059774 : ((True → ((False ∨ (True ∧ ((((((p1 ∧ False) ∨ p2) ∨ p4) → p5) ∨ p4) ∨ ((p2 ∨ ((p4 → p1) → p3)) → (False → p3))))) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_131199003697211911563367649419 : (((p4 ∧ (True → (p4 ∧ ((True ∧ p3) ∨ p2)))) → (p4 → ((p1 ∨ p3) ∨ (p2 ∧ ((p5 ∨ False) → (p2 ∨ p2)))))) ∧ ((False ∨ p3) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h11
    -- Implications on the right can always be decomposed.
    intro h12
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h14 =>
      -- False on the left can always be used.
      apply False.elim h14
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350186016037196294055006901147 : (p4 → ((((p3 → (False → p4)) ∧ p5) → ((((p1 → False) ∧ p1) ∨ p5) ∨ (((False ∨ (True → True)) ∨ ((p5 ∨ p2) ∧ p2)) ∨ p1))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339010862720070881409300433335 : (p1 → (True ∧ (((True ∧ (((p1 ∧ p3) ∧ (((False ∧ p4) ∨ ((False → p2) → p5)) ∨ p3)) ∨ p2)) ∧ (False ∨ True)) ∨ (True ∧ (p2 → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257428601306914789947595696226 : ((p3 ∨ True) → ((((p1 → (False → ((p4 ∨ p4) → p5))) ∨ (p5 ∧ (True ∧ (p2 ∨ (False ∧ p2))))) → ((p3 → (p5 ∨ p5)) ∧ p5)) ∨ True)) := by
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
theorem thm_5_vars_133976920492988307695464929915 : (((((p4 → (((p4 → ((p5 ∧ (p3 ∨ p1)) ∧ (p5 ∨ True))) ∧ p2) ∧ ((p3 ∧ p4) ∨ p1))) ∧ False) ∧ p4) ∨ True) ∨ (p4 ∨ (p5 → True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_623515049701663136199332938172 : ((((False ∨ (((False → True) ∧ (p1 ∧ (p1 ∨ False))) ∨ (p2 → (True ∧ ((p5 ∨ (((p1 ∧ True) → True) ∨ (p4 ∨ p1))) ∧ p2))))) ∨ p4) ∨ p5) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250990610779919500321061942421 : ((p1 → p5) ∨ (((((((True ∨ p3) → p4) ∧ (p2 ∨ p2)) → (((p2 → p5) ∧ p5) ∨ p1)) → ((p4 → True) → p4)) ∨ (True → True)) ∨ p2)) := by
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
theorem thm_5_vars_614455000618743067312606650853 : ((((((p1 ∨ (p4 ∧ (p4 → (p2 ∨ (p3 → ((False ∨ ((p3 → p5) → p1)) ∧ p4)))))) ∧ p4) ∧ ((p3 ∧ (p4 ∧ False)) → p3)) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_147678311016613293629762218008 : ((((((True → p1) ∨ (False → p3)) → ((p1 ∨ (p2 → (p3 ∧ p3))) → False)) ∧ ((p3 → p4) ∨ True)) → p4) ∨ ((p3 ∧ p1) ∨ (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255747121049897753646870381257 : ((True ∨ True) → (((True → (p1 ∧ p3)) → (((p1 ∨ (((p1 ∨ p2) → p3) ∧ p3)) ∨ p3) → p3)) ∨ ((False ∨ p2) ∧ (False ∨ (p1 ∧ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h7 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h8 := h3 h7
        -- We need to get the right conjuct of h8 based on <expert-advice>.
        let h9 := h8.right
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- One of the premise coincides with the conclusion.
        exact h12
    case inr h13 =>
      -- One of the premise coincides with the conclusion.
      exact h13
  case inr h14 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h15
    -- Implications on the right can always be decomposed.
    intro h16
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
        have h19 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h15, we can now drive its conclusion.
        let h20 := h15 h19
        -- We need to get the right conjuct of h20 based on <expert-advice>.
        let h21 := h20.right
        -- One of the premise coincides with the conclusion.
        exact h21
      case inr h22 =>
        -- Conjunctions on the left can always be decomposed.
        let h23 := h22.left
        let h24 := h22.right
        -- One of the premise coincides with the conclusion.
        exact h24
    case inr h25 =>
      -- One of the premise coincides with the conclusion.
      exact h25



