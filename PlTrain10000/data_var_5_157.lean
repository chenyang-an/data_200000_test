variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612188967906782584965978247000 : (((((((p3 ∧ p1) → (p5 ∨ (p3 → False))) ∧ (p2 ∧ (((p4 ∨ True) ∧ (p1 ∧ (p2 ∨ p3))) ∧ (True ∨ p1)))) ∧ (p2 ∧ False)) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_310143864778977867754274071337 : (p2 ∨ (((((((p4 → p3) ∧ p2) → (p1 → p1)) ∧ True) → (p2 ∧ p3)) ∨ p5) → ((p1 ∧ (True ∧ False)) ∨ (p2 → (p3 → (False → p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58050193080895607158082674333 : (((False ∧ False) ∧ (p4 ∨ (p4 ∨ ((p2 → (p3 ∨ (True ∧ p4))) ∧ (p3 ∧ (((((p2 ∧ False) ∨ p4) ∨ False) ∧ (p2 ∧ p1)) → p3)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213235227208099852796718757114 : ((((p2 ∧ p3) → p1) ∧ False) ∨ (True → ((((((p5 ∨ (p2 ∨ (p4 ∨ False))) ∨ ((p3 ∧ (p1 ∨ p3)) ∨ p1)) ∨ p3) ∨ False) → p3) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135483161802517794991460857653 : ((((True ∧ (p2 ∧ (False → p2))) → ((p2 ∧ (((p3 ∨ (p5 ∧ p5)) ∧ True) ∨ p5)) → p2)) → ((False → p3) ∧ p5)) ∨ (True ∧ (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51224457961042395970997947317 : ((((((p3 ∨ p1) ∧ p2) ∧ p1) ∧ ((p1 ∧ (p5 → (p3 → ((True ∧ p1) ∧ p4)))) → p4)) ∨ ((False → (p3 ∧ (p4 ∧ p2))) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320045716385626129399053266461 : (p4 ∨ ((p1 ∧ (False ∧ False)) ∨ (p5 → (((p1 → (False ∨ ((True ∨ ((p5 ∧ p4) ∨ p4)) ∧ p1))) ∨ False) ∨ (((p4 → p4) → True) → p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_52177609514545047677347700272 : (((((p3 → ((True → p2) ∨ True)) ∧ p4) → ((p1 → ((p1 → p4) → p2)) ∧ p4)) → ((((p4 ∨ False) ∨ (p4 ∨ p2)) ∨ True) ∨ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193824343277214571263825193333 : ((p5 ∧ ((p3 ∨ True) → ((p3 ∧ (p1 → True)) ∨ True))) → (((p5 ∧ ((False ∨ p3) → (p3 → (p4 ∧ p1)))) → ((False ∨ p3) ∨ p2)) ∨ True)) := by
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
theorem thm_5_vars_197800262822823676549081611203 : ((((p3 ∧ p5) ∨ False) ∨ ((False ∧ p4) ∧ True)) ∨ (((p4 ∧ (((p5 ∧ (False ∨ True)) ∧ False) → ((p3 ∧ (True → p1)) → p5))) ∧ True) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255322163946599876585422338277 : ((p5 ∧ True) → ((True → (((p4 → (((p4 → False) ∧ p5) ∧ (p5 ∨ p2))) → p4) → (p2 ∨ False))) ∨ (p5 ∨ (p5 ∨ (p3 → (p2 ∧ True)))))) := by
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
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55087544695666708750926202949 : (((p1 → (True ∧ ((False → True) ∨ p4))) ∧ (True → (False ∨ ((((p3 ∧ (True ∧ True)) ∨ p1) ∨ ((p5 ∧ p5) ∨ True)) ∧ (p3 → p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149679027436975739048016730995 : ((p5 ∧ (((p4 ∧ p2) ∧ ((((p4 → (p2 → p3)) → True) ∨ ((p1 ∧ p2) ∨ False)) ∧ (p2 ∧ p3))) ∨ p1)) ∨ (False → (p2 → (p4 ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209410837685778505899878114536 : ((p2 → (((False → p1) ∨ p1) ∧ p3)) → ((True → ((((((p5 → True) → p2) ∨ True) → p2) → p2) ∨ True)) ∧ (((True ∨ p5) ∨ True) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54629786171211452019186006374 : ((((((p3 ∨ p5) ∧ p2) → (p5 ∨ p4)) ∧ p4) → (((p2 ∨ (((p4 ∨ ((p4 ∧ False) ∨ p2)) → (p4 ∧ p5)) ∧ True)) → p1) ∨ p4)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_118144266214775071501423699699 : ((False ∨ (((p5 ∧ (p1 ∨ False)) ∧ (((p5 ∧ (p5 ∨ True)) ∨ p5) → False)) ∨ (((((False ∧ p4) → p3) ∨ p5) ∨ p2) ∨ p5))) ∨ (p3 ∨ p3)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216582914299221230882209075850 : ((((p3 ∨ p5) ∧ True) ∧ True) → (((p2 ∧ ((True → (((True ∨ p1) ∧ ((p5 ∧ p5) ∨ True)) ∧ False)) ∧ p2)) ∧ ((p3 ∧ p5) ∨ False)) → p1)) := by
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
  let h7 := h6.left
  let h8 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h1.left
    let h13 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h12.left
    let h15 := h12.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h16 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h17 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h18 := h7 h17
      -- We need to get the right conjuct of h18 based on <expert-advice>.
      let h19 := h18.right
      -- False on the left can always be used.
      apply False.elim h19
    case inr h20 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h21 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h22 := h7 h21
      -- We need to get the right conjuct of h22 based on <expert-advice>.
      let h23 := h22.right
      -- False on the left can always be used.
      apply False.elim h23
  case inr h24 =>
    -- False on the left can always be used.
    apply False.elim h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_626050604502247637846158029228 : ((((p2 → (p1 ∧ ((p4 → (p5 ∧ (((p4 ∨ p1) ∨ (p3 ∧ ((p1 ∧ (False ∧ p5)) ∧ p3))) → p2))) → ((p3 → p4) ∨ p3)))) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_659856479295573916563832352294 : (((((p1 → ((p1 ∧ p2) ∧ ((p1 → ((True ∧ p4) → ((p1 ∧ ((False ∨ p5) → p5)) → p2))) ∨ (p3 ∨ True)))) ∧ p5) → (p1 ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609640016878424689792729832059 : (((((False ∨ (((p2 → p4) ∨ ((((p3 ∧ p5) ∧ (p1 ∧ ((p1 ∨ p4) ∧ (p4 ∧ p3)))) → (p2 ∧ False)) → p1)) ∧ True)) ∨ True) ∨ p5) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191108529008977204698545547741 : (((p2 ∧ (p5 ∨ p2)) ∧ ((p5 ∨ (p3 → p2)) → p2)) ∨ (((p5 ∧ p1) → (p5 ∧ (False → (p2 ∨ p3)))) ∨ (False ∧ (True → (True ∨ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68865437707432116751305758129 : ((p4 → (True ∧ ((((p3 ∧ True) → True) → ((p1 → ((((p3 → (True ∨ True)) ∧ p1) ∧ p2) ∧ p5)) ∧ ((p4 ∧ False) ∨ False))) → p3))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((p3 ∧ True) → True) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352492764809787716943659606047 : (p4 → ((True → (p2 ∨ p2)) → (p5 → (((((p1 ∨ ((False ∨ p2) ∨ p3)) ∧ p1) ∧ False) ∧ False) ∨ (((p5 ∨ p3) → p3) ∨ (p4 ∨ p5)))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191846784082623957759515757866 : ((p3 ∨ (p2 ∧ ((p2 ∧ False) ∧ ((p1 → True) ∨ False)))) ∨ ((p3 ∨ True) ∨ ((False ∨ ((p5 ∧ ((p5 ∧ p4) ∧ (p4 ∧ p5))) ∧ p2)) ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53997645597479421817546481988 : ((((p3 → (p5 → (True ∧ ((p5 → p2) ∨ p2)))) ∨ True) → (p4 → (((p1 ∧ (p1 → False)) ∨ p3) ∨ (p4 ∧ (False ∨ (p4 ∧ True)))))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_763420164393691025835612287842 : (((p3 ∧ (False ∧ (((((p3 ∨ (p1 ∨ (p3 → ((False ∧ False) → (True → p4))))) → p1) ∧ p3) ∨ (p4 → ((True → p2) ∨ p3))) ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115299404818080569417309429172 : (((((p4 ∧ ((False ∨ (True → p5)) → p1)) ∧ p5) → p1) → (p1 ∨ (True → (((p5 ∧ False) ∨ p1) ∨ (True ∨ (p3 ∨ p1)))))) ∨ (p4 → False)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351764124452515557256087788781 : (p4 → (((p5 ∨ (p4 → True)) ∧ (p4 ∨ ((p2 → (p4 → p1)) → (p5 ∧ p3)))) → (True → ((p3 ∨ ((p2 → (p5 → p2)) ∧ p1)) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193578199391276241526738354580 : (((p4 ∨ p3) → (((p2 ∧ p3) → (False → p2)) ∧ p3)) → ((((((False ∨ p4) ∨ p5) ∧ p3) ∧ (((p2 ∧ True) ∧ p4) ∧ p4)) ∨ p5) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349246833763090833268535125312 : (p3 → (p1 → ((p2 ∧ False) ∨ (False ∨ ((p1 ∨ p5) ∧ ((((p1 ∧ ((p5 → ((p1 → p3) → p5)) → p5)) ∧ p1) ∨ p2) → (p5 ∨ p1))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48780620016677508103984218729 : ((((p5 ∨ p2) → ((p2 ∨ p2) ∧ ((p3 ∨ (((p4 → (p5 ∧ ((p3 ∨ p2) → False))) ∨ p1) ∨ False)) → p2))) ∧ ((p2 ∨ p3) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59295574627702938480410583149 : (((p3 ∨ p5) ∨ ((((((p4 ∧ p1) → p1) → p1) ∨ p4) → ((True ∧ p3) ∧ ((p1 → p2) → (False → False)))) ∧ (p3 ∧ (p5 ∨ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172280297515245261640758276806 : (((p1 ∧ (((p1 ∨ p5) ∧ p2) ∨ (p3 ∧ p4))) ∨ ((True → (p5 ∨ False)) ∨ True)) ∨ ((p1 ∨ ((p3 → ((True ∧ p4) → p3)) → False)) → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122368060033700403761178783246 : (((((p3 → (((p1 ∨ True) → True) → p1)) → ((False ∧ ((((False ∨ p4) ∧ p3) ∨ False) → False)) → p5)) ∨ p1) ∨ (p5 ∧ p1)) → (p5 → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h5 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50442137141611906387763954426 : (((False ∨ (p2 → ((((p2 ∧ ((p1 ∧ p1) ∨ (p4 ∨ False))) ∧ p5) ∧ (p3 ∧ p5)) ∨ (True → False)))) ∨ (p5 → (True → (p5 → p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_627781493417089419417811100152 : (((((((True → p2) ∨ ((p5 ∨ p4) ∨ (p5 → (False ∨ (p4 ∧ ((p5 → False) ∨ p5)))))) → ((False → (p2 ∨ p2)) → False)) ∧ p3) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41300018127030870197874195206 : ((((p3 ∨ (p3 ∧ ((((False ∨ (True ∨ (p1 → False))) → p1) ∧ p3) ∧ (p2 ∨ (p4 ∧ False))))) → (((p5 → p3) → p1) ∨ p1)) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704465637221586624031651400019 : ((((((p4 ∨ p5) → p1) → (False → ((p2 ∧ p2) → p5))) → ((p5 ∧ (p2 ∧ ((p5 ∧ p1) ∧ ((p5 → (False ∧ True)) ∨ p3)))) → p3)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h7.left
  let h10 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h11 =>
    -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
    have h12 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h11, we can now drive its conclusion.
    let h13 := h11 h12
    -- We need to get the left conjuct of h13 based on <expert-advice>.
    let h14 := h13.left
    -- False on the left can always be used.
    apply False.elim h14
  case inr h15 =>
    -- One of the premise coincides with the conclusion.
    exact h15
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356838185237276068981936196538 : (p5 → (((p4 ∧ (p1 → True)) ∧ False) ∨ (p4 ∨ ((((p1 → p3) → (p5 ∧ False)) ∧ ((((p3 ∨ (True ∨ True)) ∨ True) ∧ False) → True)) ∨ True)))) := by
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
theorem thm_5_vars_219489027519053237386686760825 : ((p5 ∨ ((p5 ∨ p1) ∧ False)) → ((((True → (p1 ∧ ((p2 ∧ True) ∧ False))) ∧ (p3 → (((True → p3) → (False ∧ True)) ∧ p2))) ∧ p2) → p1)) := by
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
  cases h1
  case inl h7 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h9 := h5 h8
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
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
theorem thm_5_vars_636048589595136318436392047701 : (((((True ∧ (p5 ∨ (((True → ((False → p4) ∨ p3)) → p5) ∧ (p2 → (p4 ∧ p2))))) ∧ ((p5 → (p2 ∨ p4)) ∧ (p3 ∧ p2))) → p5) ∨ p4) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h3.left
    let h8 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h3.left
    let h15 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h18 : (True → ((False → p4) ∨ p3)) := by
      -- Implications on the right can always be decomposed.
      intro h19
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h16
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h20 := h12 h18
    -- One of the premise coincides with the conclusion.
    exact h20
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47584792449783797163657450817 : (((p2 → (((((p1 ∧ p2) ∧ (p2 → (p4 ∧ (False ∧ (p2 → (p1 ∧ p1)))))) ∨ True) → ((p5 ∨ p1) ∨ p1)) → False)) ∨ (True ∨ p5)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_105086773312715359545000633502 : ((((((p4 → False) ∧ (p4 → ((((p1 ∧ p4) → (p3 ∨ p4)) ∧ (p1 → p4)) → p3))) ∧ p4) ∨ p2) ∨ ((p5 ∨ True) ∨ p3)) ∧ (p3 → True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_521692374515441565015865428010 : ((((p2 → True) → ((((((((False ∨ (p3 → (p4 ∨ (p2 ∨ (p4 ∧ p1))))) ∨ (p3 ∨ p3)) → False) → p5) ∨ p3) → p3) ∨ True) ∧ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116348312901001096196432332416 : ((((False ∨ True) ∨ p1) → (((False ∨ p5) ∨ (((p4 → (p1 ∧ True)) → (p2 ∧ p1)) ∧ ((True → p1) ∨ p1))) → (p3 ∧ p1))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351404305134235572327954379459 : (p4 → ((((True ∧ (p5 ∧ ((p3 → (p2 ∧ p1)) ∧ (p4 → p5)))) ∧ p1) ∨ (p2 → ((p2 → p5) ∨ False))) ∨ ((True → False) ∨ (True ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214972625575842291572053316105 : (((p3 ∧ p4) → (p4 → p1)) ∨ ((p5 ∨ ((((p3 → ((True ∧ (p1 ∧ p4)) ∨ ((p2 → p1) → p4))) ∨ False) ∨ p1) ∨ True)) ∨ (p1 ∨ False))) := by
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
theorem thm_5_vars_229859160470277656840837283587 : ((p5 → (False ∨ p1)) ∨ ((((p4 ∨ (p5 → p3)) ∨ p1) ∧ (p5 ∧ (True ∧ p2))) → ((p1 → p5) → (((True ∧ p4) → (p5 → p1)) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- Conjunctions on the left can always be decomposed.
      let h7 := h4.left
      let h8 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h4.left
      let h13 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h15
  case inr h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h4.left
    let h18 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46921344047323049284851280547 : (((((False ∨ ((p5 ∧ True) ∨ p3)) ∨ (((p1 ∨ p4) ∨ (((p3 → p3) ∨ (p4 → p2)) ∧ True)) → (p3 ∧ p2))) ∨ True) ∨ (p4 → p4)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111621354335335693265419135449 : (((((p5 → (((p3 ∨ (False ∧ True)) ∨ False) → (((False ∧ p2) ∧ (p4 ∨ (p1 → p3))) → (True → False)))) → p4) ∨ True) ∨ p5) ∨ (p3 ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263584903944599024049977163586 : (True ∧ ((False ∨ (((p1 ∨ ((p1 → ((p2 ∨ (p3 ∨ ((p4 ∧ False) → p4))) ∧ True)) → p2)) ∨ p3) → p1)) ∨ ((False → p4) ∨ (p3 ∨ p3)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217625308349295757967572145840 : ((((False ∧ p3) → False) → False) → (p4 ∨ ((p4 ∨ ((p2 → ((p3 ∨ ((p4 ∧ False) ∨ p2)) ∨ p4)) ∨ (p1 ∨ ((False ∨ p1) ∨ p5)))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207889993470056519086542421914 : ((((False → p5) → p1) ∧ (p1 ∧ p5)) → ((((p1 ∧ (p2 ∧ ((p5 ∧ p2) → (False → p3)))) ∨ p5) → p1) ∨ (p2 ∨ (p3 ∨ (p2 → p2))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314946887953001406541975315938 : (p3 ∨ (((p5 → ((((p4 ∧ p1) → p2) → p1) → p2)) ∨ p5) → (((p4 ∨ (False ∧ (((p4 ∧ (True ∨ p3)) ∧ False) ∨ p3))) ∨ True) ∨ p3))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_28075193836534288627002672895 : (((p4 → p5) → ((p5 ∨ ((p4 ∨ ((((p2 ∨ p2) → p5) ∧ (((p1 ∧ True) ∧ True) → p2)) ∧ p1)) ∧ (p3 → (p2 → False)))) → p5)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h8 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h9 := h1 h8
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Conjunctions on the left can always be decomposed.
      let h13 := h11.left
      let h14 := h11.right
      -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
      have h15 : ((p1 ∧ True) ∧ True) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h12
        -- True on the right can always be proven directly.
        apply True.intro
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h14, we can now drive its conclusion.
      let h16 := h14 h15
      -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
      have h17 : (p2 ∨ p2) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h16
      -- We have shown the premise of h13, we can now drive its conclusion.
      let h18 := h13 h17
      -- One of the premise coincides with the conclusion.
      exact h18
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336188809733771352000938223278 : (p1 → ((((((p3 ∨ ((p4 ∨ p3) ∧ p1)) → (p3 → True)) ∨ True) ∧ ((((True → (False ∨ p1)) → p3) → p4) ∨ p5)) ∧ (p1 → p5)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_623791876269634549153311503491 : ((((p1 ∨ ((((p2 ∧ p2) ∨ (p5 → p4)) ∧ p3) → (((p2 ∨ (p2 ∨ True)) ∨ p1) → ((p4 ∨ ((p1 → p5) ∧ False)) ∨ True)))) ∨ p2) ∨ p3) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h1.left
      let h6 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h1.left
        let h14 := h1.right
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h15 =>
          -- Conjunctions on the left can always be decomposed.
          let h16 := h15.left
          let h17 := h15.right
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
        -- Conjunctions on the left can always be decomposed.
        let h20 := h1.left
        let h21 := h1.right
        -- Disjunctions on the left can always be decomposed.
        cases h20
        case inl h22 =>
          -- Conjunctions on the left can always be decomposed.
          let h23 := h22.left
          let h24 := h22.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h25 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
  case inr h26 =>
    -- Conjunctions on the left can always be decomposed.
    let h27 := h1.left
    let h28 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h27
    case inl h29 =>
      -- Conjunctions on the left can always be decomposed.
      let h30 := h29.left
      let h31 := h29.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h32 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231202995546771778437474123245 : (((p3 ∨ p1) ∨ p1) → (((True ∧ (p5 → (True → ((p2 → ((True ∧ p1) → True)) → (p5 ∧ p5))))) → (False ∧ False)) → ((True ∧ p3) ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h6 : (True ∧ (p5 → (True → ((p2 → ((True ∧ p1) → True)) → (p5 ∧ p5))))) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Implications on the right can always be decomposed.
        intro h7
        -- Implications on the right can always be decomposed.
        intro h8
        -- Implications on the right can always be decomposed.
        intro h9
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h7
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h10 := h2 h6
      -- We need to get the left conjuct of h10 based on <expert-advice>.
      let h11 := h10.left
      -- False on the left can always be used.
      apply False.elim h11
  case inr h12 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h13 : (True ∧ (p5 → (True → ((p2 → ((True ∧ p1) → True)) → (p5 ∧ p5))))) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h14
      -- Implications on the right can always be decomposed.
      intro h15
      -- Implications on the right can always be decomposed.
      intro h16
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h14
      -- One of the premise coincides with the conclusion.
      exact h14
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h17 := h2 h13
    -- We need to get the left conjuct of h17 based on <expert-advice>.
    let h18 := h17.left
    -- False on the left can always be used.
    apply False.elim h18
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h19 =>
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h21 : (True ∧ (p5 → (True → ((p2 → ((True ∧ p1) → True)) → (p5 ∧ p5))))) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Implications on the right can always be decomposed.
        intro h22
        -- Implications on the right can always be decomposed.
        intro h23
        -- Implications on the right can always be decomposed.
        intro h24
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h22
        -- One of the premise coincides with the conclusion.
        exact h22
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h25 := h2 h21
      -- We need to get the left conjuct of h25 based on <expert-advice>.
      let h26 := h25.left
      -- False on the left can always be used.
      apply False.elim h26
    case inr h27 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h28 : (True ∧ (p5 → (True → ((p2 → ((True ∧ p1) → True)) → (p5 ∧ p5))))) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Implications on the right can always be decomposed.
        intro h29
        -- Implications on the right can always be decomposed.
        intro h30
        -- Implications on the right can always be decomposed.
        intro h31
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h29
        -- One of the premise coincides with the conclusion.
        exact h29
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h32 := h2 h28
      -- We need to get the left conjuct of h32 based on <expert-advice>.
      let h33 := h32.left
      -- False on the left can always be used.
      apply False.elim h33
  case inr h34 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h35 : (True ∧ (p5 → (True → ((p2 → ((True ∧ p1) → True)) → (p5 ∧ p5))))) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h36
      -- Implications on the right can always be decomposed.
      intro h37
      -- Implications on the right can always be decomposed.
      intro h38
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h36
      -- One of the premise coincides with the conclusion.
      exact h36
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h39 := h2 h35
    -- We need to get the left conjuct of h39 based on <expert-advice>.
    let h40 := h39.left
    -- False on the left can always be used.
    apply False.elim h40



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352815783715903145449990492458 : (p4 → ((p5 ∨ p3) → ((((False ∧ (p1 → (((p3 ∧ (p1 ∧ True)) → False) ∧ p1))) ∧ p4) ∨ (p5 ∨ (p5 ∨ p3))) ∨ ((p5 ∧ p3) → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41319168076247198576970383867 : ((((((p5 ∨ p4) ∧ p2) → (True ∨ (p1 ∧ (p4 → ((p2 ∧ (p1 ∨ False)) ∨ True))))) ∧ ((p2 ∨ ((p5 → p4) ∨ p3)) ∨ p5)) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358537992139446987490575198990 : (p5 → (p2 → ((((p4 → False) → p4) → ((False ∨ ((False ∨ False) ∨ (p4 ∧ p2))) ∧ ((p5 ∨ p1) → False))) ∨ ((True ∨ True) ∨ (True ∧ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164456303277711267510055603438 : ((((True ∧ ((p5 ∨ (p4 → ((p3 → p2) ∧ False))) → (p2 ∨ (p3 ∧ p2)))) ∧ p2) ∧ p1) ∨ (((p1 → False) → p2) → ((True ∨ p1) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326942200074188993128788038869 : (True → (((((True ∧ (False → p2)) ∧ ((p5 ∨ p2) → (p1 ∧ ((p4 → p1) → p4)))) ∨ (p4 ∨ ((p4 ∨ p3) ∨ True))) ∧ (p3 ∨ False)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164681474659031927496695479752 : (((((p4 ∧ True) ∧ ((True ∧ p4) ∨ (True → (p4 ∨ ((p4 ∨ p5) ∨ p2))))) ∧ p4) ∨ True) ∨ (((False → ((p4 ∧ p4) ∨ True)) → p4) ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2643147724671239815799091467 : (((((p2 ∨ p5) → p2) → False) ∧ p4) ∨ ((p5 ∧ (p1 → p4)) → ((p1 → (False ∨ ((False ∧ p1) → (p2 ∨ (True ∧ p4))))) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_666398729987556084808611246820 : (((((False ∧ ((((False → (True ∧ p4)) → p5) → (False ∨ (False → (p5 → p4)))) → p5)) ∨ (True ∨ (p2 ∧ p1))) ∧ ((p3 → p4) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_648023720082971344767300620415 : ((((((((False ∨ False) → (p5 → p2)) → ((p3 ∧ p2) ∧ (p4 → p4))) ∨ (((False → p3) ∨ p1) → (p5 → p1))) ∧ p1) ∧ (p4 ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180621221737420407393788729332 : (((p5 ∧ (True ∧ ((p5 ∨ p4) → p3))) ∧ ((p3 ∨ False) ∧ (p2 → p5))) → (((p3 → p2) ∨ (p3 ∨ (p2 ∧ p3))) ∧ ((p4 → p3) ∨ p3))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h3.left
  let h9 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11
  -- Conjunctions on the left can always be decomposed.
  let h12 := h1.left
  let h13 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h12.left
  let h15 := h12.right
  -- Conjunctions on the left can always be decomposed.
  let h16 := h15.left
  let h17 := h15.right
  -- Conjunctions on the left can always be decomposed.
  let h18 := h13.left
  let h19 := h13.right
  -- Disjunctions on the left can always be decomposed.
  cases h18
  case inl h20 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h20
  case inr h21 =>
    -- False on the left can always be used.
    apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53856573006657276835866848260 : (((((p1 → p5) → False) ∨ ((p3 → (True → p1)) ∨ False)) ∨ (((p3 → (True ∨ (p2 → p5))) ∨ p2) ∨ ((p3 ∨ (True ∨ True)) → True))) ∨ p4) := by
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
theorem thm_5_vars_135589477766610907637980114334 : ((((((p3 → p2) ∨ p4) → ((p5 ∧ (p5 ∨ p3)) → (False → p4))) → (p3 ∧ p2)) ∨ ((p4 ∧ (p3 → p4)) ∨ p1)) ∨ ((p2 → p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190869687727857764688229232457 : (((((p1 ∨ p2) ∧ p4) ∨ (p5 → p5)) → (p5 ∨ False)) ∨ ((p2 ∧ (((p4 ∨ p1) ∨ ((True ∧ (p1 ∧ False)) ∧ p4)) → (True ∧ p1))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194169845761740496353950454301 : ((p2 → (((False → p1) → ((p5 → p3) ∧ False)) → False)) → (True → (((p2 ∨ ((True → (p2 ∨ p3)) ∨ False)) ∨ p1) → ((p5 ∨ p1) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- False on the left can always be used.
        apply False.elim h8
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326865354845351339543203879380 : (True → ((((p4 ∧ (p3 ∧ (p5 → (((p2 → (p1 ∨ ((((p2 ∧ p2) → p1) ∧ p3) ∨ (p5 ∨ False)))) ∨ p3) ∧ p5)))) ∨ True) ∨ False) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312571737268513518584327459809 : (p3 ∨ ((((p3 → (((p2 ∨ p1) ∧ (False ∨ p2)) ∨ ((((p5 ∧ False) → (p2 → True)) ∨ ((p3 → p2) ∧ p2)) ∨ p2))) ∨ False) ∨ p4) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224374240950111958843609081445 : ((False → (p4 → p5)) ∧ ((((p2 → (p3 → False)) ∨ p1) ∨ p2) ∨ (((((p3 ∨ p5) ∨ False) ∧ p3) → p2) ∨ (False → ((p3 ∨ p1) ∨ p2))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147511638891528061288223239971 : (((p3 ∨ ((p2 ∧ ((p5 ∨ False) ∧ ((p5 → ((False ∧ p5) ∧ True)) ∧ ((p4 → False) → True)))) → p3)) ∨ p3) ∨ (((p1 ∨ p3) ∨ p4) → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h9 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h10 := h7 h9
    -- We need to get the left conjuct of h10 based on <expert-advice>.
    let h11 := h10.left
    -- We need to get the left conjuct of h11 based on <expert-advice>.
    let h12 := h11.left
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44967173890676169214429022199 : ((((True → False) ∧ (((p3 ∨ (True → (p4 ∨ p4))) ∧ (((p1 → (p2 → (p2 ∧ p1))) ∨ p5) ∨ ((False → p2) → True))) ∨ p2)) → p1) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h10 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h11 := h2 h10
          -- False on the left can always be used.
          apply False.elim h11
        case inr h12 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h13 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h14 := h2 h13
          -- False on the left can always be used.
          apply False.elim h14
      case inr h15 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h16 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h17 := h2 h16
        -- False on the left can always be used.
        apply False.elim h17
    case inr h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h20 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h21 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h22 := h2 h21
          -- False on the left can always be used.
          apply False.elim h22
        case inr h23 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h24 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h25 := h2 h24
          -- False on the left can always be used.
          apply False.elim h25
      case inr h26 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h27 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h28 := h2 h27
        -- False on the left can always be used.
        apply False.elim h28
  case inr h29 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h30 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h31 := h2 h30
    -- False on the left can always be used.
    apply False.elim h31



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_634302580292205820116550169489 : (((((True → (((((p5 ∧ (True ∨ True)) ∧ (p2 ∨ (p3 → p2))) → (p4 ∧ (p1 → True))) → (p3 → True)) → p5)) → (p2 → p1)) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175912190284094222908479986087 : ((((p5 ∧ p5) ∨ (((((p3 ∧ p5) ∨ p4) ∧ p5) ∨ p1) ∧ True)) ∨ True) ∧ ((True ∨ p5) → (p5 ∨ ((p2 → p5) → (p1 → (p2 → p1)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263692766014617442783055854107 : (True ∧ ((((True ∨ (p4 → p3)) ∨ ((p3 → (p1 → p4)) → (p3 ∧ p5))) → ((p2 ∨ p1) ∨ p4)) ∨ (True ∨ ((p1 ∨ p3) ∨ (p2 ∨ False))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265075196335488836322187547154 : (True ∧ (True ∧ (True → (True → (False ∨ ((p2 ∧ ((((((p5 ∨ p5) → p3) ∨ p5) ∨ ((p4 ∨ p4) ∧ p3)) ∨ p5) ∨ (p1 ∧ p2))) ∨ True)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_322492737034382362105804400801 : (p5 ∨ (((True ∧ p4) → ((((p5 → (p3 → ((p4 ∧ p3) → p2))) ∨ False) ∨ ((p5 ∧ True) ∨ (((True ∨ p1) ∨ p4) → False))) ∨ True)) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_654396099234542908925941019257 : ((((((p4 ∨ (p1 ∨ (p1 ∨ (p5 ∧ p2)))) ∨ ((False → (True → (p4 ∧ ((True ∨ p2) ∨ p3)))) ∧ (True ∨ p1))) ∨ False) ∨ (p1 ∨ p5)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115384414530461406209713017423 : ((((True ∨ (p1 ∨ p5)) → ((p4 ∧ p5) ∧ p5)) ∧ ((p2 → ((p1 ∨ (True → (p3 ∨ (p4 → (p5 ∨ p1))))) ∨ p3)) ∨ p5)) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46056886048122481403213753313 : (((((p5 ∨ (p2 ∧ (((p5 → (((p2 → (p2 ∨ p5)) → True) ∨ (p2 ∨ p5))) → p3) → (p1 ∨ p2)))) ∧ p2) ∨ p3) ∧ (False ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303250406957479746067721992149 : (False ∨ (p5 → ((p2 → (p5 ∨ (p5 ∧ (p3 ∧ (False ∨ p2))))) ∧ (((p2 ∨ p4) → p2) → ((((p5 → p2) → False) ∨ False) ∨ (False → p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45431065230963292068727947674 : (((True ∨ ((((True ∧ ((p5 ∧ True) ∨ (p2 ∧ (True ∧ (True ∨ (p1 ∧ p3)))))) ∨ p4) → (p5 ∨ ((p5 ∧ p1) ∨ p3))) → p3)) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172423084794738961300505251938 : ((((True ∧ p1) → (p5 ∧ False)) ∧ (p2 ∧ ((p3 ∧ p2) ∨ ((p3 → True) ∧ p2)))) ∨ ((p1 ∧ ((True ∧ p3) ∨ (False → True))) ∨ (True ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148655932196350304533873042180 : ((((p3 → p5) ∨ ((p5 ∧ (p5 ∧ p3)) ∨ p3)) ∧ (p5 ∧ (p2 ∧ (((p3 → False) ∧ (False ∨ True)) ∨ p3)))) ∨ ((p1 ∨ (True ∧ True)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47192449570707191278595679355 : (((((False ∧ ((p1 → p1) → ((p2 ∧ p4) ∨ p5))) ∨ (True → p4)) ∨ (p3 → (p3 ∨ (False ∧ (True ∨ (p2 ∨ p4)))))) ∨ (False ∧ p5)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179343891622358967901210427804 : ((p1 ∨ (p4 ∧ ((((p4 → True) → p2) ∧ p3) ∨ (p3 ∨ (True ∧ p1))))) ∨ ((((p2 ∧ p2) → p2) ∨ True) → ((False ∧ (p3 ∨ p3)) → False))) := by
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
theorem thm_5_vars_113349252467511102014331168010 : (((p1 ∧ (((((p2 ∨ ((p5 ∧ False) ∧ p4)) → p3) → (p2 ∧ False)) ∨ True) ∨ (p5 ∨ ((p4 ∧ p4) → False)))) ∧ (True ∧ p5)) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224266238050054532979072113317 : ((False → (True ∧ p4)) ∧ (((((False ∧ p2) ∨ ((p2 ∨ (p1 ∧ p2)) ∨ p1)) ∨ (p1 → (((p4 ∧ p1) ∧ (False → p5)) → p5))) ∧ p5) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_599633842311068498982523415136 : (((((True → p5) ∨ (p2 ∧ (p2 → ((p4 ∨ (False → False)) → ((((((False ∨ p4) ∨ p3) ∨ p5) ∨ p2) → (p3 → p1)) ∨ p5))))) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228914610929587455423328469172 : ((p4 ∨ (False ∨ p1)) ∨ ((p4 ∧ p5) ∨ ((False ∨ (((((p1 ∧ p5) ∨ (False ∧ True)) ∧ ((False ∧ p5) → p3)) → (p1 → p4)) ∨ True)) ∨ p4))) := by
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
theorem thm_5_vars_137758986165428340887877063606 : ((p2 ∨ (((p4 ∨ False) → (p3 ∨ (((((p3 ∧ (((p4 ∧ p3) ∧ True) ∨ p1)) ∨ p1) → p2) ∧ p3) ∧ p4))) → p4)) ∨ (p2 → (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_652602595090332429883471224023 : ((((False ∨ ((p2 ∨ ((p4 ∨ p3) → p2)) ∧ (((p1 ∧ (((False → p4) ∧ p3) ∨ p2)) → p1) → ((p2 ∨ p1) ∧ p5)))) ∧ (True ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254721761897663214681394338415 : ((p3 ∧ p3) → (((((False ∨ p5) ∨ p2) ∧ p3) ∧ p5) → (p3 ∧ (((p2 ∨ True) ∧ p1) ∨ (((((p2 ∨ p4) ∧ True) ∨ p2) ∨ p2) ∨ True))))) := by
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
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h1.left
      let h11 := h1.right
      -- One of the premise coincides with the conclusion.
      exact h11
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h1.left
    let h14 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h14
  -- Conjunctions on the left can always be decomposed.
  let h15 := h2.left
  let h16 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h17 := h15.left
  let h18 := h15.right
  -- Disjunctions on the left can always be decomposed.
  cases h17
  case inl h19 =>
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- False on the left can always be used.
      apply False.elim h20
    case inr h21 =>
      -- Conjunctions on the left can always be decomposed.
      let h22 := h1.left
      let h23 := h1.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h24 =>
    -- Conjunctions on the left can always be decomposed.
    let h25 := h1.left
    let h26 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64362034544151223709022575680 : ((p1 ∨ (((p2 ∨ (p5 ∨ ((p5 → p3) ∨ (True → ((p2 ∧ p1) ∨ ((p3 → p1) → p2)))))) ∨ ((p3 ∨ (p3 ∨ p3)) → p3)) ∨ False)) ∨ p3) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- One of the premise coincides with the conclusion.
      exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206791123936354950405373015433 : ((p4 → (False ∨ (p2 ∨ (True → p3)))) ∨ ((((p1 ∨ p5) ∨ p5) ∨ (False ∨ ((p1 ∨ (((p1 → (p3 → p3)) → p3) → False)) ∨ p3))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



