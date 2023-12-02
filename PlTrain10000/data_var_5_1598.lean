variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184151828938961383735316922618 : (((p1 ∨ ((p2 → True) → ((p3 ∨ (p5 ∨ p5)) ∨ p4))) ∨ True) ∨ (((p2 → (p2 ∧ (p3 ∧ p2))) ∧ False) ∨ ((p1 ∧ (p1 → p5)) ∧ False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305757395566762373879408172540 : (p1 ∨ (((((p5 ∧ (p5 → p5)) ∧ p2) ∨ p2) ∧ p4) ∨ ((p3 → (False ∧ p4)) → ((True → (True → (p1 ∧ (p5 ∧ (p4 ∧ p3))))) → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
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
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244740567475207509681615445364 : ((p1 ∧ False) ∨ (((((False ∨ (p1 → p2)) → (((False ∧ (p2 ∨ p2)) ∨ (False → p2)) ∨ p3)) ∨ (False → (p2 ∧ (p3 ∧ p5)))) → p5) → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((False ∨ (p1 → p2)) → (((False ∧ (p2 ∨ p2)) ∨ (False → p2)) ∨ p3)) ∨ (False → (p2 ∧ (p3 ∧ p5)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150540552411930985188177479230 : ((((p4 ∨ ((True ∧ (False → (p1 ∨ p4))) → p2)) → ((((p1 ∨ p2) ∨ p1) ∧ False) ∧ (p1 ∧ p1))) ∧ p2) → (p3 → ((False → p3) → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : (p4 ∨ ((True ∧ (False → (p1 ∨ p4))) → p2)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h10 := h4 h6
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172360204001769265596585586348 : ((((p5 ∧ (False ∨ True)) ∧ (True ∧ p2)) ∨ (((p1 ∨ p1) ∨ True) ∨ (False → p2))) ∨ (False → ((((p3 ∧ False) → (True → p5)) ∨ p1) → p1))) := by
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
theorem thm_5_vars_117881735730587441257840767425 : ((p5 ∧ (((p3 → True) → (((((p1 → p1) → p3) ∧ p3) ∨ False) ∧ ((p3 ∨ ((False ∨ p4) → (p5 ∧ False))) ∨ False))) → False)) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233034057201473728160216108360 : ((p4 ∧ (p4 ∧ p5)) → (p5 ∧ (p3 ∨ (((((p4 → p2) → p1) ∨ (False ∧ (p3 ∨ (p1 → p2)))) ∨ ((p2 ∧ p5) ∨ (p4 ∨ p5))) ∨ p3)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
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
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319865249047529616841270045851 : (p4 ∨ ((((p2 → p4) → True) → False) ∨ (((((p5 ∨ p3) → ((True → p3) → p5)) → ((((p1 ∨ p2) ∨ False) ∧ p1) → p3)) ∨ True) ∨ False))) := by
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
theorem thm_5_vars_63901266515632108433751587245 : ((False ∨ (((p4 ∨ (((False ∧ (p2 → p4)) ∨ p1) ∧ p2)) ∧ ((p2 → (p5 → (((p3 → p3) → True) ∨ (p4 ∨ p1)))) ∧ p2)) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115447136191262565605280630236 : ((((p2 ∨ (p3 ∧ False)) ∧ (p4 ∧ (False ∨ p3))) ∨ (True ∨ ((p4 → ((True → True) ∨ True)) → ((p3 ∧ p4) ∨ (p5 ∧ p4))))) ∨ (p4 → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337524371128116531194168404021 : (p1 → ((((p1 → ((p5 → p2) ∧ ((p1 ∧ p4) → (p5 ∨ (((p3 ∨ p4) ∨ p5) ∧ p4))))) ∧ p5) → False) ∨ (p2 → ((p2 ∨ p4) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655660624521643832068845062027 : (((((((((True → (p4 ∨ (True ∨ True))) → False) → True) ∨ ((p4 → True) ∧ (p5 ∧ p5))) → p3) ∧ ((p2 ∨ p2) ∨ p3)) ∨ (False ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250881410903577617401322400803 : ((p1 → p3) ∨ ((p3 ∧ (((True → (p4 ∧ (((p3 ∨ True) ∨ p2) → (p1 → True)))) → (p1 ∨ p3)) ∧ ((p3 ∨ False) ∨ p1))) ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199024722906137056972522566320 : ((((p2 ∨ (p2 ∨ (p5 → True))) ∧ p1) ∧ p2) → ((((((p5 ∨ (p1 → True)) → p2) ∨ p2) → (p3 ∨ (p3 ∨ p2))) ∧ (p5 ∨ False)) ∨ p1)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157412448059733899035186143821 : ((((p4 ∧ (((p2 ∧ (p5 ∧ p5)) ∧ False) → p2)) → ((p5 → (p1 ∧ False)) ∨ p3)) ∧ (False ∧ p4)) ∨ (p1 ∨ (True → ((False → False) ∧ True)))) := by
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
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204350795922505491305595778061 : (((False ∨ (True ∧ (False ∨ False))) ∧ p5) ∨ ((((((p2 ∨ ((False → p2) ∨ (p5 ∧ (True ∧ p1)))) → p1) ∧ p3) → p4) → (p4 → p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173301329231950374770942006941 : ((p1 → ((False ∧ (p2 → p2)) ∧ ((True ∨ p5) → (p1 → (p2 ∨ (p3 ∨ p2)))))) ∨ (p5 ∨ (True ∨ (p2 → (p5 ∧ (False ∨ (p1 ∧ False))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114739145591931354239649307810 : ((((p4 ∧ (True → False)) ∨ ((False ∨ ((p5 → True) ∧ p5)) ∨ (p2 ∧ (p2 ∧ False)))) → (p4 ∨ ((True → (p5 ∨ p3)) → False))) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148863438643847665196312968088 : (((p5 ∨ ((p3 → False) ∨ p3)) ∧ (p1 → (p2 ∨ (p4 ∧ ((((p1 → False) ∧ p1) ∨ (p3 ∧ p2)) ∧ p4))))) ∨ (((p5 ∧ p5) ∧ p1) → p1)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135378353060926702676882950958 : ((((False ∧ (p4 ∨ (p3 ∨ ((p5 ∨ p1) ∧ (p5 ∧ (True ∨ ((p4 → p4) ∨ p5))))))) ∨ p1) ∨ (p3 → (p3 → True))) ∨ (p3 ∨ (False ∧ p2))) := by
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
theorem thm_5_vars_113580789538524457247790544929 : (((p1 ∧ (((p5 ∧ p5) ∧ (((p2 ∧ (p5 → p2)) ∧ p5) → True)) ∧ (((p3 ∨ (p4 ∨ p4)) ∨ p5) → False))) ∨ (False → True)) ∨ (p3 ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679940895616409397472297118827 : (((((((p1 ∨ ((p5 ∨ ((p5 ∧ ((p1 → False) ∧ p5)) ∨ p4)) ∨ True)) → p2) ∨ (False → True)) → p3) → (p5 ∨ ((p2 ∨ False) ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219278957693580442669927852636 : ((p1 ∨ (p3 → (True ∧ p1))) → (((((p2 → False) ∨ (False → p2)) ∨ (True ∧ (((p4 → p5) → True) → (True ∨ (False ∨ p5))))) → False) ∨ True)) := by
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
theorem thm_5_vars_702866725632256912096324223409 : (((((p4 → ((p1 ∧ True) → p3)) ∨ ((False ∨ p4) ∧ p2)) ∨ ((p3 → p4) ∧ ((((True ∧ (p1 ∧ True)) ∨ True) ∨ p3) ∨ (p4 ∨ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301786404789740757051488267828 : (False ∨ ((p2 ∧ p1) ∨ (((p3 ∧ (False ∧ (p3 → False))) ∨ ((p5 ∧ (p4 ∨ p5)) ∧ (p1 ∧ p3))) → (p4 → (False ∨ ((p5 ∧ p1) → p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h10.left
      let h15 := h10.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h16
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- One of the premise coincides with the conclusion.
      exact h18
    case inr h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h10.left
      let h21 := h10.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h22
      -- Conjunctions on the left can always be decomposed.
      let h23 := h22.left
      let h24 := h22.right
      -- One of the premise coincides with the conclusion.
      exact h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64805813617686749153979592543 : ((p2 ∨ ((p5 ∨ ((((((p3 ∧ ((p3 → (p5 → p3)) ∧ p3)) ∨ p1) ∧ p5) ∧ p2) ∨ False) ∨ (((p4 → p4) ∨ p1) → True))) ∨ p3)) ∨ p5) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119487082388796031512239318752 : ((p4 → (p1 ∨ ((p2 → (False ∨ p5)) ∧ (((p5 → p5) → (((p3 ∧ (p5 ∨ (p5 ∧ False))) → (False ∨ p3)) → p2)) ∨ p2)))) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336249288115463182600697197305 : (p1 → ((((False ∧ ((True → False) ∧ (p5 ∧ ((p2 ∧ (p1 ∨ False)) ∧ (p2 → p1))))) ∨ True) ∧ ((p1 ∨ (True ∧ p5)) ∧ (False ∧ False))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186678753871860775678584387549 : (((p4 ∧ (((p1 ∨ p1) → p1) ∨ False)) ∧ (p3 → (p2 ∨ p1))) → (((p3 ∧ p1) → ((p4 → p2) ∨ (False ∨ p4))) ∧ (p4 ∧ (p1 ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h10
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h11 := h1.left
  let h12 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h13 := h11.left
  let h14 := h11.right
  -- Disjunctions on the left can always be decomposed.
  cases h14
  case inl h15 =>
    -- One of the premise coincides with the conclusion.
    exact h13
  case inr h16 =>
    -- False on the left can always be used.
    apply False.elim h16
  -- Conjunctions on the left can always be decomposed.
  let h17 := h1.left
  let h18 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h19 := h17.left
  let h20 := h17.right
  -- Disjunctions on the left can always be decomposed.
  cases h20
  case inl h21 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h19
  case inr h22 =>
    -- False on the left can always be used.
    apply False.elim h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156739653994728428430916177889 : (((((p4 → (p5 ∧ p5)) → p3) → ((((p5 ∧ False) ∨ ((p2 ∨ p4) → p2)) ∧ True) → p4)) ∧ True) ∨ (((p2 ∧ (p3 ∧ False)) ∧ p5) → p1)) := by
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
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_782408020665005687448890498727 : (((p3 ∨ (((p2 → (((p4 ∧ (True → (p5 → p1))) ∨ (((False → p2) → p2) ∨ ((False → p2) ∨ (p4 → p2)))) ∧ True)) → p3) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117059209696725288338034849608 : (((p5 ∨ p1) → ((((True ∧ p4) → False) → p2) → (((p4 ∨ ((p2 ∨ (((p4 ∨ p4) ∨ p1) ∨ p5)) → p3)) → p2) ∧ p4))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780977583359827851356590945721 : (((p2 ∨ ((True ∧ (True → p4)) → ((((p2 ∧ p2) ∧ p3) ∧ (True ∧ ((((p1 ∧ p5) → ((True → p5) ∧ p1)) ∧ p2) ∨ p3))) ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310652998477218079273052847188 : (p2 ∨ ((((p1 ∨ False) → p4) ∧ p5) → ((((p2 ∨ p3) → (p5 → (True ∧ (((p2 → False) ∧ (p4 ∨ p4)) ∧ p5)))) → (p5 ∧ False)) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682481047148539569005164043381 : ((((((p3 → (p4 ∧ ((((False ∧ p2) ∧ p5) ∨ p5) ∨ p3))) → p2) → ((True → p5) → p5)) ∧ ((p2 ∧ p4) → (p2 ∧ (p1 ∨ p4)))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6
  -- Conjunctions on the left can always be decomposed.
  let h8 := h5.left
  let h9 := h5.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185865447883150365406789859804 : (((((((p1 ∨ (p3 ∧ True)) ∧ p4) ∨ p1) → True) → p3) ∧ p1) → ((True → p2) → ((((p4 ∧ p4) ∨ p2) ∧ (p5 ∧ p5)) ∨ (p3 ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : ((((p1 ∨ (p3 ∧ True)) ∧ p4) ∨ p1) → True) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352806744472303512498663761133 : (p4 → ((p4 ∨ True) → ((((p2 → (p3 ∨ ((((((p3 → False) ∧ p1) ∧ p5) ∧ p4) ∨ p4) ∨ False))) ∨ p5) ∧ ((p2 ∨ p3) ∧ p3)) ∨ p4))) := by
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
theorem thm_5_vars_178695838879296666176852588533 : ((((p4 ∧ p3) ∧ (p1 ∧ p2)) ∨ ((((False ∧ True) ∧ p3) ∧ p1) ∨ True)) ∨ ((p3 → (p5 ∨ False)) ∧ (((True → p5) ∨ p4) ∧ (p2 ∨ p1)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255665303578013537971071534820 : ((p5 ∧ p5) → ((((False ∨ (True → (p3 ∨ (p1 ∨ p1)))) → ((((p4 → ((p4 ∨ p5) → p1)) → (p2 ∧ p2)) ∨ p4) ∨ False)) ∧ True) ∨ True)) := by
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
theorem thm_5_vars_350857910724911032135666561466 : (p4 → (((False ∧ (p4 ∧ p2)) ∨ (((False ∨ (((p2 → False) → p3) ∧ p4)) → p4) ∧ (((p1 ∨ p5) ∨ (p1 ∧ p5)) ∨ True))) ∧ (p4 ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_665169964928229162348587794041 : (((((((((p1 ∨ ((p2 → p3) ∨ (p3 → (p2 → p5)))) ∧ (p3 → p3)) ∨ (p2 ∨ p5)) → p2) ∨ p1) ∧ True) ∧ ((p2 → True) → True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258279447221905162421727122260 : ((p5 ∨ True) → (((p5 ∨ ((p1 ∨ (p3 ∨ p4)) ∨ True)) ∧ (((p3 ∧ (p4 → ((True ∨ False) ∨ p1))) ∨ (True → (p2 ∧ p5))) ∧ p5)) ∨ True)) := by
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
theorem thm_5_vars_310549936633856859499969560047 : (p2 ∨ ((p1 ∨ (p5 ∨ ((p4 ∨ p4) ∨ False))) → (True ∧ (((p4 → ((p4 ∨ p5) → p2)) ∨ (True ∨ p1)) ∨ (((False ∨ p5) ∨ False) → False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h8 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h9 =>
        -- False on the left can always be used.
        apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260498708837953781339929574383 : ((p3 → False) → ((p4 ∨ p4) ∨ (p2 ∨ ((((p3 ∨ False) ∧ p3) ∧ (p5 → (False ∨ (((p1 ∨ p5) ∧ (p5 ∨ p2)) → p2)))) → (p5 ∧ p5))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h8 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h9 := h1 h8
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h10
  -- Conjunctions on the left can always be decomposed.
  let h11 := h2.left
  let h12 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h13 := h11.left
  let h14 := h11.right
  -- Disjunctions on the left can always be decomposed.
  cases h13
  case inl h15 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h16 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h14
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h17 := h1 h16
    -- False on the left can always be used.
    apply False.elim h17
  case inr h18 =>
    -- False on the left can always be used.
    apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638670116453337143803724269572 : (((((((p5 ∨ (p5 ∨ p4)) ∨ p2) → p5) → ((((p1 ∧ False) → ((False → (p4 → p5)) ∨ (p4 → p1))) ∨ (True → p1)) ∧ p3)) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134253946874156673954310503819 : (((((True → False) ∧ p1) ∨ (((False ∨ p3) → (True ∧ p1)) ∧ (((p2 ∨ p3) ∧ (True → p3)) ∨ (p2 → p5)))) ∨ p3) ∨ (False → (p3 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313162788893010645949122631183 : (p3 ∨ (((p5 → ((p3 ∨ (p2 ∧ True)) ∧ (((False → p3) ∨ True) ∧ False))) → ((p5 → (p1 ∧ False)) ∨ (p2 → ((False → p1) ∨ False)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2848407324506742590017939572 : ((p3 ∨ (p3 ∨ (True ∧ p5))) → (((((p2 ∨ (p2 ∨ p2)) ∧ (True ∧ (p4 → p5))) ∧ (p3 → (False ∧ False))) → p5) ∨ (p5 → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
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
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h11 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h12 := h5 h11
      -- We need to get the left conjuct of h12 based on <expert-advice>.
      let h13 := h12.left
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h7.left
        let h17 := h7.right
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h18 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h2
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h19 := h5 h18
        -- We need to get the left conjuct of h19 based on <expert-advice>.
        let h20 := h19.left
        -- False on the left can always be used.
        apply False.elim h20
      case inr h21 =>
        -- Conjunctions on the left can always be decomposed.
        let h22 := h7.left
        let h23 := h7.right
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h24 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h2
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h25 := h5 h24
        -- We need to get the left conjuct of h25 based on <expert-advice>.
        let h26 := h25.left
        -- False on the left can always be used.
        apply False.elim h26
  case inr h27 =>
    -- Disjunctions on the left can always be decomposed.
    cases h27
    case inl h28 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h29
      -- Conjunctions on the left can always be decomposed.
      let h30 := h29.left
      let h31 := h29.right
      -- Conjunctions on the left can always be decomposed.
      let h32 := h30.left
      let h33 := h30.right
      -- Disjunctions on the left can always be decomposed.
      cases h32
      case inl h34 =>
        -- Conjunctions on the left can always be decomposed.
        let h35 := h33.left
        let h36 := h33.right
        -- We want to use the implication h31 based on <expert-advice>. So we show its premise.
        have h37 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h28
        -- We have shown the premise of h31, we can now drive its conclusion.
        let h38 := h31 h37
        -- We need to get the left conjuct of h38 based on <expert-advice>.
        let h39 := h38.left
        -- False on the left can always be used.
        apply False.elim h39
      case inr h40 =>
        -- Disjunctions on the left can always be decomposed.
        cases h40
        case inl h41 =>
          -- Conjunctions on the left can always be decomposed.
          let h42 := h33.left
          let h43 := h33.right
          -- We want to use the implication h31 based on <expert-advice>. So we show its premise.
          have h44 : p3 := by
            -- One of the premise coincides with the conclusion.
            exact h28
          -- We have shown the premise of h31, we can now drive its conclusion.
          let h45 := h31 h44
          -- We need to get the left conjuct of h45 based on <expert-advice>.
          let h46 := h45.left
          -- False on the left can always be used.
          apply False.elim h46
        case inr h47 =>
          -- Conjunctions on the left can always be decomposed.
          let h48 := h33.left
          let h49 := h33.right
          -- We want to use the implication h31 based on <expert-advice>. So we show its premise.
          have h50 : p3 := by
            -- One of the premise coincides with the conclusion.
            exact h28
          -- We have shown the premise of h31, we can now drive its conclusion.
          let h51 := h31 h50
          -- We need to get the left conjuct of h51 based on <expert-advice>.
          let h52 := h51.left
          -- False on the left can always be used.
          apply False.elim h52
    case inr h53 =>
      -- Conjunctions on the left can always be decomposed.
      let h54 := h53.left
      let h55 := h53.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h56
      -- Conjunctions on the left can always be decomposed.
      let h57 := h56.left
      let h58 := h56.right
      -- Conjunctions on the left can always be decomposed.
      let h59 := h57.left
      let h60 := h57.right
      -- Disjunctions on the left can always be decomposed.
      cases h59
      case inl h61 =>
        -- Conjunctions on the left can always be decomposed.
        let h62 := h60.left
        let h63 := h60.right
        -- One of the premise coincides with the conclusion.
        exact h55
      case inr h64 =>
        -- Disjunctions on the left can always be decomposed.
        cases h64
        case inl h65 =>
          -- Conjunctions on the left can always be decomposed.
          let h66 := h60.left
          let h67 := h60.right
          -- One of the premise coincides with the conclusion.
          exact h55
        case inr h68 =>
          -- Conjunctions on the left can always be decomposed.
          let h69 := h60.left
          let h70 := h60.right
          -- One of the premise coincides with the conclusion.
          exact h55



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149250650130717437561436627462 : (((p2 ∨ p1) ∨ (((p3 ∧ (p5 → p1)) ∨ (p3 ∧ True)) ∨ (True ∧ ((p3 ∧ p1) ∧ (p5 ∧ (p4 → p2)))))) ∨ ((p2 ∨ (False → p2)) ∨ p4)) := by
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
theorem thm_5_vars_345678069607505105577389081078 : (p3 → ((p2 ∨ ((((p3 → p4) ∨ True) ∧ False) ∨ (((((p5 ∧ p4) ∨ p3) ∧ p4) → (p3 ∧ (False ∧ ((False → p2) ∧ p5)))) ∧ False))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111559286699798978691582158680 : ((((((True → ((p2 ∨ p5) ∧ p2)) ∨ ((False → True) ∧ True)) ∧ (((p1 ∨ ((p3 ∧ p3) ∨ p1)) → True) ∧ p4)) ∧ p1) ∨ True) ∨ (p1 → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339601054184443519717774889609 : (p1 → (p2 ∨ (((((p3 ∧ ((False ∨ (True → p5)) ∨ p5)) ∧ ((p4 → (p3 ∧ ((p2 → False) ∨ (p4 ∧ p3)))) ∧ p4)) ∧ True) ∧ p4) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41531404569965345231003323932 : ((((((((p3 → p1) → p5) ∨ p3) ∨ (True ∧ p1)) ∧ p5) ∨ (p2 ∨ ((p5 ∨ p4) ∧ ((p4 ∨ (p2 → (p2 → p4))) ∧ p3)))) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244929127104793016179679614307 : ((p1 ∧ p3) ∨ (((((p1 ∧ True) ∧ ((p4 ∧ ((p1 ∧ (p2 ∧ (False ∨ p1))) → (p5 ∨ p5))) ∧ p3)) ∧ False) ∧ (p4 ∧ True)) ∨ (False → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60477804725647130925959826389 : (((p5 → p5) → (((True ∨ False) ∧ p4) ∨ (p2 → ((((p5 ∨ p1) ∧ (((p4 ∨ p3) ∨ (p1 → False)) ∨ True)) ∧ (p4 ∧ p1)) ∨ p2)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136383638438437934613476581313 : ((((True → False) ∨ (p1 ∧ p5)) ∨ (True ∧ ((p3 ∧ True) ∨ ((((p4 ∧ p3) ∨ p3) ∧ False) ∨ (p3 ∨ (False → True)))))) ∨ ((p1 ∨ False) ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179413836050556907153475021198 : ((p4 ∨ (((False ∨ p4) ∧ (p1 ∧ (p3 ∧ ((p2 ∧ p4) ∨ p2)))) ∨ p5)) ∨ ((p2 → ((((True → False) ∧ (p5 → p3)) → p5) ∨ p5)) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161910386609143659341607126603 : ((p1 → (((p4 ∧ (p1 → p4)) ∨ ((p2 → (p4 ∨ p3)) → ((p3 ∨ p5) ∨ p3))) ∧ (p3 ∨ p1))) → (((p5 ∧ p5) → p1) ∨ (False → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69174905757249603988099478945 : ((p5 → (((p4 ∧ p2) ∨ (True ∧ (True ∨ (p5 → (True → (False ∧ (p4 → (True → p4)))))))) → (False ∨ (p4 ∨ (p2 → (p2 ∨ p4)))))) ∨ False) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
      have h12 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h1
      -- We have shown the premise of h11, we can now drive its conclusion.
      let h13 := h11 h12
      -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
      have h14 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h13, we can now drive its conclusion.
      let h15 := h13 h14
      -- We need to get the left conjuct of h15 based on <expert-advice>.
      let h16 := h15.left
      -- False on the left can always be used.
      apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358598359514551095718980416401 : (p5 → (p3 → (((((((p4 → p1) → p3) → p3) → p2) ∧ ((False → (p4 ∧ (p3 ∧ p2))) → p4)) ∧ p1) ∨ ((True ∨ (False → p4)) ∨ p3)))) := by
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
theorem thm_5_vars_9386803343200228563296005852 : ((((((True → p2) → p1) ∧ p4) ∨ (p5 → (True → (((p1 ∨ p4) → (p3 → (p4 ∨ p4))) ∨ (True ∨ ((p3 ∧ p2) ∨ p1)))))) ∨ p5) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678221994291374288305254639830 : ((((((p5 ∨ False) ∨ (p3 ∨ ((p2 ∧ (True ∨ p4)) → p5))) ∨ ((p3 ∨ (p3 ∨ p5)) ∧ (False → False))) ∨ ((p1 ∨ (False → p1)) ∨ p4)) ∨ p2) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152602432022195350780988860100 : (((p3 ∧ p1) ∧ (p1 ∨ ((p2 ∨ (False ∨ True)) → ((False → False) ∧ ((p1 ∧ (True ∨ p4)) ∨ (p1 → p5)))))) → ((p2 → (True → p4)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
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
theorem thm_5_vars_233892642132891727153083329092 : ((p4 ∨ (p3 ∨ p3)) → (((p1 → True) ∨ p4) → (((False → (p2 ∧ p2)) → (p1 ∧ ((p1 → (p2 ∨ p3)) ∨ ((p4 ∨ p5) ∧ p5)))) ∨ True))) := by
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
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265533894368475426239188954108 : (True ∧ (False ∨ (((p3 ∧ (((p2 ∨ False) ∧ p3) ∨ (True ∨ ((p3 ∨ False) ∨ True)))) ∨ p3) → ((((p5 ∧ (p3 → p4)) ∨ p4) → p1) ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h9 =>
        -- False on the left can always be used.
        apply False.elim h9
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
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
        case inr h16 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
  case inr h17 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62184020756730057197339967885 : ((p3 ∧ (((p4 → ((p5 ∨ (p4 ∨ ((p1 → False) ∧ p4))) ∧ (((True ∧ ((True → p1) ∧ p5)) ∧ p4) → (True → p3)))) ∧ p4) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156598371497101409079363681796 : (((((p5 ∧ ((p1 → ((True ∨ (((False → p2) → p5) ∧ p4)) → True)) ∨ p2)) → False) ∧ p2) ∧ p2) ∨ (False → (p5 → ((False ∨ p5) → False)))) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59399711806763665087728419939 : (((True → p2) ∨ (p4 ∨ ((p1 ∧ (p1 ∧ (p4 → (True ∨ ((p3 ∧ True) ∨ p3))))) ∨ (((p3 ∧ True) → (p4 → p2)) → (p2 ∨ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180321071400176275939321517361 : ((((p5 ∨ (True ∨ p2)) ∨ (p5 ∨ (p3 → (p3 ∧ p3)))) ∧ (p2 ∨ p3)) → ((((False → (p5 ∨ (p4 → p1))) → p1) ∧ p1) ∨ (False → p4))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h7
        -- False on the left can always be used.
        apply False.elim h7
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h9
        -- False on the left can always be used.
        apply False.elim h9
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h13
          -- False on the left can always be used.
          apply False.elim h13
        case inr h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h15
          -- False on the left can always be used.
          apply False.elim h15
      case inr h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h17 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h18
          -- False on the left can always be used.
          apply False.elim h18
        case inr h19 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h20
          -- False on the left can always be used.
          apply False.elim h20
  case inr h21 =>
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h22 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h23 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h24
        -- False on the left can always be used.
        apply False.elim h24
      case inr h25 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h26
        -- False on the left can always be used.
        apply False.elim h26
    case inr h27 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h28 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h29
        -- False on the left can always be used.
        apply False.elim h29
      case inr h30 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h31
        -- False on the left can always be used.
        apply False.elim h31



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199632532469046093651998182826 : (((((p1 → p2) ∨ p2) ∨ (p4 → False)) → p1) → (p2 ∨ (((((p3 → p1) ∨ p2) ∧ ((True ∧ True) ∨ p5)) ∨ p5) ∨ (False → (True ∧ False))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69586230250771330217489386230 : (((((p5 ∧ p5) ∧ ((((p3 ∨ (True ∧ p5)) → (p1 → p4)) → False) ∧ ((True ∨ (p2 ∧ (p2 ∨ p4))) ∨ (p4 ∨ p3)))) ∧ p4) ∧ True) → p1) := by
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
  let h8 := h6.left
  let h9 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h7.left
  let h11 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h14 : ((p3 ∨ (True ∧ p5)) → (p1 → p4)) := by
        -- Implications on the right can always be decomposed.
        intro h15
        -- Implications on the right can always be decomposed.
        intro h16
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h17 =>
          -- One of the premise coincides with the conclusion.
          exact h5
        case inr h18 =>
          -- Conjunctions on the left can always be decomposed.
          let h19 := h18.left
          let h20 := h18.right
          -- One of the premise coincides with the conclusion.
          exact h5
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h21 := h10 h14
      -- False on the left can always be used.
      apply False.elim h21
    case inr h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h22.left
      let h24 := h22.right
      -- Disjunctions on the left can always be decomposed.
      cases h24
      case inl h25 =>
        -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
        have h26 : ((p3 ∨ (True ∧ p5)) → (p1 → p4)) := by
          -- Implications on the right can always be decomposed.
          intro h27
          -- Implications on the right can always be decomposed.
          intro h28
          -- Disjunctions on the left can always be decomposed.
          cases h27
          case inl h29 =>
            -- One of the premise coincides with the conclusion.
            exact h5
          case inr h30 =>
            -- Conjunctions on the left can always be decomposed.
            let h31 := h30.left
            let h32 := h30.right
            -- One of the premise coincides with the conclusion.
            exact h5
        -- We have shown the premise of h10, we can now drive its conclusion.
        let h33 := h10 h26
        -- False on the left can always be used.
        apply False.elim h33
      case inr h34 =>
        -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
        have h35 : ((p3 ∨ (True ∧ p5)) → (p1 → p4)) := by
          -- Implications on the right can always be decomposed.
          intro h36
          -- Implications on the right can always be decomposed.
          intro h37
          -- Disjunctions on the left can always be decomposed.
          cases h36
          case inl h38 =>
            -- One of the premise coincides with the conclusion.
            exact h5
          case inr h39 =>
            -- Conjunctions on the left can always be decomposed.
            let h40 := h39.left
            let h41 := h39.right
            -- One of the premise coincides with the conclusion.
            exact h5
        -- We have shown the premise of h10, we can now drive its conclusion.
        let h42 := h10 h35
        -- False on the left can always be used.
        apply False.elim h42
  case inr h43 =>
    -- Disjunctions on the left can always be decomposed.
    cases h43
    case inl h44 =>
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h45 : ((p3 ∨ (True ∧ p5)) → (p1 → p4)) := by
        -- Implications on the right can always be decomposed.
        intro h46
        -- Implications on the right can always be decomposed.
        intro h47
        -- Disjunctions on the left can always be decomposed.
        cases h46
        case inl h48 =>
          -- One of the premise coincides with the conclusion.
          exact h5
        case inr h49 =>
          -- Conjunctions on the left can always be decomposed.
          let h50 := h49.left
          let h51 := h49.right
          -- One of the premise coincides with the conclusion.
          exact h5
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h52 := h10 h45
      -- False on the left can always be used.
      apply False.elim h52
    case inr h53 =>
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h54 : ((p3 ∨ (True ∧ p5)) → (p1 → p4)) := by
        -- Implications on the right can always be decomposed.
        intro h55
        -- Implications on the right can always be decomposed.
        intro h56
        -- Disjunctions on the left can always be decomposed.
        cases h55
        case inl h57 =>
          -- One of the premise coincides with the conclusion.
          exact h5
        case inr h58 =>
          -- Conjunctions on the left can always be decomposed.
          let h59 := h58.left
          let h60 := h58.right
          -- One of the premise coincides with the conclusion.
          exact h5
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h61 := h10 h54
      -- False on the left can always be used.
      apply False.elim h61



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_162321747238094185113255059060 : (((((p2 → (((p5 ∧ False) → p3) → (False ∧ (p3 ∨ True)))) → (p2 ∧ False)) ∧ p5) ∨ True) ∧ (((p4 ∧ (p4 ∨ p4)) → p1) ∨ (True ∨ p2))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310672702797351964797074298938 : (p2 ∨ (((p1 ∧ p5) ∨ (p3 ∨ p4)) → (p4 ∨ (((p2 ∧ (p3 → (False ∧ (False ∧ p1)))) → (p5 ∧ p3)) ∨ (p4 ∨ (False ∨ (p5 ∨ True))))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_643177866310884082977331199737 : ((((p3 ∧ (((((p2 → (p1 ∨ p2)) → ((True ∧ p2) ∧ False)) → ((p1 ∧ False) ∧ ((p2 ∨ p1) → p1))) → p3) ∨ (p1 → p4))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138943108546820656458054334702 : (((((((p1 → (p1 → p1)) → p4) → ((p1 ∨ ((False → True) ∧ (p5 ∧ p3))) ∧ (True ∨ p2))) → p4) ∧ p5) ∨ False) → ((p4 ∧ p3) ∨ True)) := by
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
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53221303049039575960903011339 : ((((((False → False) ∨ False) ∨ p2) ∧ (((False → p1) → p3) → p1)) ∨ (((((False ∨ (False ∧ p5)) ∧ p4) ∧ (True ∨ True)) ∨ p2) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111523221040671294406887149875 : (((((((((p4 ∧ (p2 ∨ False)) ∨ ((p2 ∧ True) ∧ (p3 ∨ ((p4 → p3) ∧ p5)))) → p3) ∨ p1) ∨ True) ∧ p5) ∧ p5) ∨ True) ∨ (True → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613068316344250378637084461234 : (((((((False → False) → ((((p3 ∨ (p3 → (p5 → p5))) ∧ (((p2 ∨ True) ∨ p2) ∨ p5)) ∨ p1) ∧ p4)) ∨ p4) → (False ∧ p4)) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148094109829884801362676496841 : ((((p5 ∧ (((p5 ∧ True) → True) → (p4 ∨ ((p2 ∨ (p2 → False)) → (True → True))))) → True) → (p1 ∧ p4)) ∨ ((p4 ∨ True) ∨ (p4 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113480739896691449781394688842 : ((((((p5 ∧ (((p2 ∧ (p2 → (True → p2))) ∧ p1) → (False ∨ p1))) ∨ p4) ∨ (p2 ∧ False)) ∨ (p1 ∧ p2)) ∨ (p5 → p2)) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232973464247017058062031439445 : ((p3 ∧ (p1 → False)) → ((((p1 ∧ (p1 ∧ (p2 ∧ p4))) ∨ False) ∧ ((((p5 ∧ p5) ∧ p3) → (False ∨ p2)) → p5)) ∨ (False → (p5 → False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303939663639958189254459120716 : (p1 ∨ ((((p5 ∨ ((True ∨ p4) ∧ p2)) ∨ False) ∨ ((((((p1 ∧ p1) ∧ (p3 → p3)) ∧ p1) ∧ True) ∧ (p5 ∨ (p5 ∧ True))) → p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_664176549165683981630904344217 : ((((False ∨ (((True → p5) → (False → p5)) → ((p5 → (p3 ∧ (p1 → p2))) ∨ (False → (((p4 ∨ p4) ∨ p5) → p5))))) → (p5 ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_756100633067378416860181008177 : (((p1 ∧ ((p5 → (p2 ∧ ((((p3 → (p4 ∧ ((p2 ∧ ((p3 → p4) → p1)) → (p5 ∨ False)))) ∨ p3) ∧ (p2 ∧ p5)) → p2))) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611591551631095459071820591489 : (((((False ∨ (p2 → ((p2 ∨ (p2 ∨ ((((((p2 ∨ p2) → (p1 ∧ True)) ∨ True) ∧ p2) ∧ p5) → False))) → (p3 ∧ p2)))) → p4) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622328394803348230751163644332 : ((((p3 ∧ (((False → (p1 → p3)) ∧ (((p2 ∧ ((p2 ∧ p3) ∨ (p4 ∨ (p3 → p1)))) ∨ (True ∧ p4)) → (p2 ∧ True))) → p2)) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_2312577179396457271639571550 : (((p5 ∧ ((p3 ∧ ((p2 → True) ∨ p5)) ∧ False)) → ((p2 ∧ p3) ∨ p5)) → ((True → False) → ((p3 → (p5 ∧ (p2 → p3))) → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56927454208890411455691328478 : (((True ∨ (True → True)) ∧ (((((False → (p5 ∨ (False ∧ ((True → (False ∧ p2)) ∨ p3)))) → (p2 → p1)) ∧ p4) ∧ (p2 ∨ p5)) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60655094693670219521681528642 : ((True ∧ (((True → ((p3 ∨ ((p5 → (((False → p3) ∨ p1) ∧ p5)) → False)) ∧ (False ∨ True))) ∨ False) ∨ ((p1 → True) → (p2 → True)))) ∨ p1) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52310493277883145992416790508 : (((((((False ∨ p4) → (p2 ∨ (p5 ∧ (True ∧ p3)))) ∧ p2) ∧ p2) ∨ p1) ∧ ((p4 ∨ ((True ∨ (p3 → (True ∧ True))) ∨ False)) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153559174772471656259972265407 : ((True → (p5 ∨ (((True → (True ∧ ((p3 ∧ False) → p3))) ∨ p1) ∧ ((((p4 ∧ True) ∨ True) → p2) ∧ p1)))) → ((p2 ∨ (p5 ∧ False)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159067247957517716479845013202 : ((p5 ∨ (p1 ∧ (((p5 ∨ (p3 ∧ (((False ∧ p2) ∧ p4) → p4))) ∨ ((p1 ∨ p5) ∧ p1)) ∧ p5))) ∨ ((((p5 → p2) ∨ p3) ∨ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_169144381335794387137658238685 : ((p5 → (False ∨ ((p5 ∨ (p5 → p2)) → ((p3 ∨ p1) ∧ ((p4 → (p1 ∧ p3)) ∨ False))))) → (True ∧ (((p5 → (p4 ∧ p4)) → p4) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_639247148020616056094803824362 : (((((((True ∨ p3) → p1) ∧ False) → ((p4 → (((p1 ∨ p4) ∧ (p2 ∨ False)) ∨ (p5 ∧ (p4 ∧ (False ∧ (p5 ∧ False)))))) ∨ p5)) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113646565009398319218804651202 : (((((p5 → ((False ∧ (p4 ∧ (p5 ∧ ((p2 ∨ p3) → p1)))) ∧ (p3 ∧ (p4 ∧ p3)))) → (p4 ∧ True)) ∧ p4) → (p1 ∨ True)) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_675868291105168897096170645871 : ((((((p1 → ((p5 → (p3 ∨ ((p5 → False) ∧ p1))) ∧ p3)) ∧ p2) → ((p1 → False) ∨ (p4 → True))) ∧ ((p3 → True) → (p5 ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215757062684674449841129348400 : ((p1 ∨ ((True ∧ p1) ∨ p5)) ∨ (p2 → ((True ∧ p3) → (p1 ∨ (p5 → (p1 → ((p4 ∨ ((p4 ∧ (p2 → p5)) ∨ (p2 ∨ p5))) ∨ p5))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147807459467634118464767663757 : (((p3 ∧ (((True ∨ (p3 ∨ p4)) ∧ (p5 ∨ (((False ∨ (p4 ∧ p4)) ∨ p5) ∧ (p2 ∨ p3)))) → p5)) → p5) ∨ (p2 → (p4 ∨ (p5 → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123275158353292391592099792176 : (((True → (p5 ∧ ((p2 → True) → (True → (((False ∧ (p4 → (False ∨ True))) → p3) ∧ p1))))) ∧ ((p3 → p3) ∨ (False ∧ True))) → (p1 ∧ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : (p2 → True) := by
      -- Implications on the right can always be decomposed.
      intro h9
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h10 := h7 h8
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h11 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h12 := h10 h11
    -- We need to get the right conjuct of h12 based on <expert-advice>.
    let h13 := h12.right
    -- One of the premise coincides with the conclusion.
    exact h13
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- False on the left can always be used.
    apply False.elim h15
  -- Conjunctions on the left can always be decomposed.
  let h17 := h1.left
  let h18 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h18
  case inl h19 =>
    -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
    have h20 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h17, we can now drive its conclusion.
    let h21 := h17 h20
    -- We need to get the right conjuct of h21 based on <expert-advice>.
    let h22 := h21.right
    -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
    have h23 : (p2 → True) := by
      -- Implications on the right can always be decomposed.
      intro h24
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h22, we can now drive its conclusion.
    let h25 := h22 h23
    -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
    have h26 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h25, we can now drive its conclusion.
    let h27 := h25 h26
    -- We need to get the right conjuct of h27 based on <expert-advice>.
    let h28 := h27.right
    -- One of the premise coincides with the conclusion.
    exact h28
  case inr h29 =>
    -- Conjunctions on the left can always be decomposed.
    let h30 := h29.left
    let h31 := h29.right
    -- False on the left can always be used.
    apply False.elim h30



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304995295720092414946737145382 : (p1 ∨ ((((((True → (((p3 → (p1 ∨ p2)) ∨ p1) ∨ False)) ∧ True) ∧ (p2 → (p3 → True))) ∧ p5) ∨ (p3 → True)) ∨ (p4 → (p3 ∧ p2)))) := by
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



