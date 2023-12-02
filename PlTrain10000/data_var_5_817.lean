variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205696693905573172316459791220 : (((True → p2) ∨ (p3 → (p1 → False))) ∨ (False ∨ ((True ∧ False) ∨ ((p5 ∨ p3) ∨ (p5 ∨ (((p2 → (p3 ∧ False)) → False) ∨ (p2 ∨ True))))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_800198317779856630738976683573 : (((p2 → (((((((False → p2) ∨ p4) → p5) ∨ (p3 ∨ (p5 → (False → p5)))) ∧ ((((p5 ∧ p5) → p5) ∧ p2) ∨ False)) ∧ False) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156334093060768074751450988037 : ((True → (((p2 ∨ (((p2 ∧ p4) ∧ ((p3 → (p2 ∧ True)) ∧ p5)) ∧ (p1 ∧ p4))) ∨ True) ∨ p3)) ∧ (p2 → (False → (p5 ∨ (p2 ∧ p4))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299297450052429779416375794376 : (False ∨ ((((((p3 ∨ p5) ∧ p5) ∧ ((True ∨ p4) ∨ False)) → False) ∨ ((((((False ∨ False) → p1) ∧ True) → (p1 → p5)) ∧ False) → p1)) ∨ p1)) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_805030384451185301880590223076 : (((p3 → ((p4 → p2) → ((((p5 ∧ p5) → (p5 → (((((p4 → (True → False)) ∨ p5) ∨ p1) ∨ p4) ∧ p1))) ∧ (p2 ∧ p1)) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695847544396751934165195568260 : (((((p3 ∨ p2) ∧ (True ∨ ((True → p4) ∨ (p5 → (p1 → (p4 ∨ True)))))) → (((p1 → (p5 ∧ False)) → True) → ((p4 ∨ p2) ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_143300180050711944341463101839 : ((p4 → ((((((p5 ∨ p4) ∧ p4) ∧ False) → p4) ∨ (p2 ∧ (((p5 ∨ p2) ∧ ((True ∧ True) → p3)) ∧ p3))) ∧ p1)) → ((p2 ∨ p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57922574404893568937031076724 : (((p5 ∨ (p5 → True)) → (False ∧ (((((p2 → True) ∧ ((True ∧ True) ∧ ((True ∨ p1) ∧ False))) ∧ p2) → (False ∨ p5)) ∧ (p2 ∧ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117631782140893787259490084619 : ((p3 ∧ (((p1 → ((p4 ∧ (True ∧ True)) → (p3 ∧ ((p3 ∨ True) → True)))) ∨ (p5 ∨ ((p1 ∨ (True ∧ p4)) → p3))) ∨ p2)) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150063319874877198947112664339 : ((True → ((p3 ∧ ((p1 ∨ ((False → (False ∧ p3)) ∧ p5)) ∨ (p1 ∨ (False ∧ p3)))) ∧ (p2 ∧ (False ∨ p5)))) ∨ (p2 → ((True → True) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_776805646161340412000545435001 : (((p1 ∨ (((p1 ∧ (p4 ∧ ((False ∨ False) ∨ True))) ∧ (True ∨ ((False ∨ (p2 ∨ (p5 ∨ p1))) ∧ (p4 ∨ ((p5 ∧ False) ∨ p4))))) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134108534762484821386980435562 : (((((p5 ∨ ((p3 → p4) ∨ (p2 → ((True ∧ (p1 ∨ p2)) ∧ p4)))) ∧ (p5 ∨ (p4 → p1))) ∧ (p2 ∨ p1)) ∨ p3) ∨ ((True → False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137709742534170682295341308712 : ((p1 ∨ (((((p3 → True) → (p5 ∧ p4)) ∧ True) ∨ p4) ∨ ((p4 → p1) ∧ (True → (p3 → (True ∨ (p1 ∨ p4))))))) ∨ (p2 → (p2 ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252932578165871124155626919697 : ((True ∧ p2) → (((p2 ∧ ((((p2 ∨ ((p2 → False) ∧ (False ∧ p4))) ∨ p3) ∨ False) ∧ (p1 ∧ (((p1 → p4) → False) ∧ False)))) ∧ p5) ∨ True)) := by
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
theorem thm_5_vars_42510143879432967539543929966 : (((False ∨ ((p4 ∧ (False → p1)) ∨ (p5 ∧ (((p3 ∧ (True ∨ (p1 ∨ p5))) → ((True ∧ (p5 → (False ∨ False))) → p4)) ∨ p4)))) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178547282970330324562042695355 : (((p4 → ((p5 ∧ p5) ∧ (p4 → (p1 → p2)))) → (p2 ∨ (False ∧ False))) ∨ (True ∨ (((((True → (p3 ∨ p4)) → True) ∨ False) ∨ p4) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_805577101995334841513943558012 : (((p3 → (p5 ∨ (False ∧ (False ∧ (p3 → ((True → (((p4 ∧ (True ∧ ((p3 ∧ True) ∨ p1))) ∨ p4) ∨ ((True ∨ False) ∨ p1))) → False)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44894905926966431618350279785 : ((((False ∧ (p2 ∨ p4)) → ((((p3 ∨ True) → (p5 ∧ (True ∧ p1))) ∧ ((p4 ∧ (p4 ∧ (p2 ∧ p5))) ∨ (False ∧ True))) → p4)) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231622056421998144432290450221 : (((True ∧ p5) → p5) → ((True ∧ (((p4 → (p1 ∨ ((((p4 ∨ False) → False) ∨ p2) ∨ (((p2 → p1) ∨ p2) ∨ True)))) → p3) → p3)) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p4 → (p1 ∨ ((((p4 ∨ False) → False) ∨ p2) ∨ (((p2 → p1) ∨ p2) ∨ True)))) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48931690117345369586705906175 : (((((p5 ∧ ((p4 ∧ ((p2 ∧ (((p5 → False) ∧ p1) → p3)) ∨ (p2 ∧ p4))) ∧ p1)) → (p1 → False)) ∧ False) ∨ (True ∨ (p2 → p3))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313111437671763376469614874018 : (p3 ∨ ((((False ∨ (p4 ∧ True)) ∨ ((p5 → ((p5 → (p1 ∨ p2)) → (p4 ∨ (p3 ∧ p2)))) ∨ (p5 → p1))) ∨ (True → (p3 ∨ True))) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37841917516254148863474151306 : ((((p4 ∨ ((p3 ∧ p5) ∨ (p3 ∨ (((p5 ∧ (((p3 → (p4 ∨ p4)) ∧ (p1 → False)) ∧ True)) → (False ∧ True)) → p3)))) → p2) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615360586353235693917734713149 : (((((((p1 ∨ (False → False)) ∨ p5) ∧ ((False ∧ p3) ∨ ((False ∨ True) ∧ (p2 → p5)))) ∨ ((False ∧ p4) → (False ∨ (p1 ∧ p4)))) ∨ p2) ∨ False) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_665202587249168221913747391850 : ((((((((((p2 ∨ ((False ∧ False) → (p4 ∧ p1))) → True) → (p4 ∧ p1)) ∧ p2) → (p4 → p2)) → False) ∧ p2) ∧ (p4 ∧ (True ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303807927845687554211941893217 : (p1 ∨ ((((False ∨ (True ∧ p2)) → (p2 ∧ (p3 → (((p2 → True) ∧ (False ∧ False)) ∧ ((p1 ∨ ((p5 ∧ p1) → p5)) ∨ p1))))) → p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352089815305321535223116335495 : (p4 → (((((p3 ∧ p3) ∨ p4) ∧ p2) ∧ p5) ∨ ((((p3 → False) → p3) ∧ p3) → ((p1 ∧ (p2 ∨ (((p2 ∧ p4) ∧ p2) ∧ p1))) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_755551797114342342975191030378 : (((p1 ∧ (((((p1 → ((p4 ∨ p1) ∨ p5)) ∧ ((((p5 ∧ p4) ∧ p5) → (p4 → p1)) ∧ (True ∨ (p3 ∨ False)))) ∧ p3) ∧ p4) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39875823542930737591106858183 : (((p2 → ((((False ∧ True) ∨ (False ∧ p2)) ∧ ((p2 ∧ False) ∨ (((False ∨ (True ∧ (p3 ∨ False))) ∨ False) → False))) ∧ (p2 ∨ p2))) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48646498539509272556239026025 : (((((p2 → p1) → ((((p4 ∨ False) ∨ p5) ∨ (False → (True → False))) ∧ p5)) ∧ ((True → (p3 ∨ True)) ∨ p2)) ∧ (p2 → (p3 → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226210701122586482279770104767 : (((p2 ∨ p2) ∨ p2) ∨ ((p4 ∨ p5) ∨ ((p4 ∨ (False → (True ∨ (p1 ∧ (((True ∧ p1) ∨ p4) ∨ False))))) ∨ (((p4 ∧ p1) → p5) ∨ True)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57617012620314981732609004924 : ((((True ∧ p3) ∨ p5) → (((p1 → (p5 ∧ (True ∨ (((p5 ∨ p4) ∧ ((p1 ∨ p3) ∨ p1)) ∨ ((p2 ∨ p2) ∧ p2))))) → True) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57363761843432584872703653120 : (((p4 ∧ (p4 ∧ p1)) ∨ ((p4 ∨ (((((p4 ∨ p1) ∧ False) → ((False ∧ p5) ∨ True)) ∧ p1) ∧ (p3 → p1))) → (p5 ∨ (p2 → True)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234342319724589154840670083599 : ((p1 → (True ∨ p3)) → (((p5 ∨ (p5 ∧ (((p5 ∨ p2) ∨ p1) → ((p2 ∧ (p3 ∨ False)) ∨ p4)))) ∧ False) ∨ (((p3 → p5) ∧ False) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322388244876496453189530848030 : (p5 ∨ ((((p5 ∧ (((((True ∧ p3) → p2) ∧ p3) ∨ True) ∧ p3)) ∨ (False → (p3 → p3))) → ((((p1 ∨ p4) ∧ p3) ∧ False) ∨ True)) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118356425175010397733347515973 : ((p2 ∨ ((False → ((((True ∧ False) ∧ p4) ∨ p2) ∧ ((p4 ∨ (p1 → ((p5 ∧ (True ∨ False)) ∧ True))) ∧ (False → True)))) → p4)) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_34205751874785968003763687402 : ((True → (((p3 ∨ ((p1 ∧ p5) ∨ True)) → (((False → (True → (p1 ∧ p3))) → False) → ((p4 ∨ p3) ∧ (p4 → p5)))) ∨ (p3 ∧ False))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h9 : (False → (True → (p1 ∧ p3))) := by
        -- Implications on the right can always be decomposed.
        intro h10
        -- Implications on the right can always be decomposed.
        intro h11
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- False on the left can always be used.
        apply False.elim h10
        -- False on the left can always be used.
        apply False.elim h10
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h12 := h3 h9
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h14 : (False → (True → (p1 ∧ p3))) := by
        -- Implications on the right can always be decomposed.
        intro h15
        -- Implications on the right can always be decomposed.
        intro h16
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- False on the left can always be used.
        apply False.elim h15
        -- False on the left can always be used.
        apply False.elim h15
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h17 := h3 h14
      -- False on the left can always be used.
      apply False.elim h17
  -- Implications on the right can always be decomposed.
  intro h18
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h19 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h20 : (False → (True → (p1 ∧ p3))) := by
      -- Implications on the right can always be decomposed.
      intro h21
      -- Implications on the right can always be decomposed.
      intro h22
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h21
      -- False on the left can always be used.
      apply False.elim h21
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h23 := h3 h20
    -- False on the left can always be used.
    apply False.elim h23
  case inr h24 =>
    -- Disjunctions on the left can always be decomposed.
    cases h24
    case inl h25 =>
      -- Conjunctions on the left can always be decomposed.
      let h26 := h25.left
      let h27 := h25.right
      -- One of the premise coincides with the conclusion.
      exact h27
    case inr h28 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h29 : (False → (True → (p1 ∧ p3))) := by
        -- Implications on the right can always be decomposed.
        intro h30
        -- Implications on the right can always be decomposed.
        intro h31
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- False on the left can always be used.
        apply False.elim h30
        -- False on the left can always be used.
        apply False.elim h30
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h32 := h3 h29
      -- False on the left can always be used.
      apply False.elim h32
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_803738122156463138881855701173 : (((p3 → ((((p3 → (((p5 → (p5 ∨ (p3 ∨ p4))) ∨ (p1 → p4)) ∧ (p2 ∨ p4))) ∧ (p4 → True)) ∨ (p5 ∧ p5)) ∧ (False ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179110377819041121176236453671 : ((False ∧ (p5 ∧ ((p3 ∧ p4) → ((p1 → ((p4 → True) ∨ True)) → p5)))) ∨ ((p2 ∨ ((p2 ∧ p4) → True)) ∨ (((p5 ∧ p3) → p3) → p2))) := by
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
theorem thm_5_vars_64120766590829931197313276354 : ((False ∨ (((p5 ∨ (p1 ∨ p5)) ∨ (p5 ∨ p3)) → (((True ∨ (False → p1)) ∧ (((p3 → True) → (p2 → False)) ∧ p2)) → (p5 ∨ p2)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h7
        case inr h12 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h12
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h14
      case inr h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
  case inr h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h4.left
    let h18 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h19 =>
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h20 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h20
      case inr h21 =>
        -- Disjunctions on the left can always be decomposed.
        cases h21
        case inl h22 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h18
        case inr h23 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h23
    case inr h24 =>
      -- Disjunctions on the left can always be decomposed.
      cases h24
      case inl h25 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h25
      case inr h26 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300069245169701483112675363672 : (False ∨ (((p5 ∧ ((p1 ∨ ((((((p2 ∨ p5) ∨ ((True ∨ True) → p3)) ∧ p1) ∨ p2) ∧ p1) ∧ (False ∧ p3))) ∧ p1)) ∨ p4) ∨ (True ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112839960271819881328006579542 : ((((p4 ∨ (p1 ∧ (False → p2))) → (((False ∧ (False → False)) ∧ (((((p5 → p1) → p4) ∨ p5) ∨ p5) → p2)) → p5)) → False) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703258283939549184396994415545 : ((((p2 ∧ (p4 ∨ ((p2 → ((p4 → True) ∧ p4)) ∧ p2))) ∨ ((((((True → False) → p5) ∧ (p3 ∨ True)) → p3) ∨ p1) → (False ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55520639583617409584219961250 : ((((True → p2) ∨ (p4 ∨ (True ∨ p2))) → (((((p3 ∨ (p3 ∨ p4)) ∧ (p1 ∧ True)) ∨ False) → (p5 ∧ (True → p4))) ∨ (p4 ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218990168369150364156690406945 : ((p4 ∧ (p1 ∧ (p4 ∨ p2))) → ((p3 ∧ ((((p1 ∧ p1) ∧ p5) ∨ ((False ∨ (p3 → p2)) ∧ True)) ∧ p1)) ∨ ((p1 ∨ p1) → (False → p5)))) := by
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
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40660632790340103928280350296 : (((((((((p2 ∨ True) ∧ p2) ∨ (True ∨ p1)) ∧ (True ∨ p5)) → ((((False → p4) ∨ False) → True) ∨ p4)) ∨ (p2 → p5)) → False) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58179657122643048057413456059 : (((p3 ∧ p2) ∧ (True → ((p3 ∨ False) ∧ (False ∧ ((((p4 ∧ (((p5 → True) → (False ∧ False)) ∨ (p2 → p2))) → True) → False) → True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310523968384439228625142136154 : (p2 ∨ (((p4 → (True ∧ (True ∧ p3))) ∧ p4) → ((((p4 ∨ True) ∧ p2) ∧ ((p1 ∨ False) ∧ ((True ∧ p3) ∧ p4))) → (p1 → (p3 ∨ p2))))) := by
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
  cases h6
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h5.left
    let h10 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h10.left
      let h13 := h10.right
      -- Conjunctions on the left can always be decomposed.
      let h14 := h12.left
      let h15 := h12.right
      -- Conjunctions on the left can always be decomposed.
      let h16 := h1.left
      let h17 := h1.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h18 =>
      -- False on the left can always be used.
      apply False.elim h18
  case inr h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h5.left
    let h21 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h21.left
      let h24 := h21.right
      -- Conjunctions on the left can always be decomposed.
      let h25 := h23.left
      let h26 := h23.right
      -- Conjunctions on the left can always be decomposed.
      let h27 := h1.left
      let h28 := h1.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h29 =>
      -- False on the left can always be used.
      apply False.elim h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350213028816789377930243838388 : (p4 → (((False ∨ p2) ∧ ((False ∨ ((((p4 → (p2 → (p5 → p3))) ∧ (p1 → ((p2 ∨ p2) ∨ p5))) ∨ p5) → (p3 ∧ p2))) ∨ p5)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48929828537644847111929629670 : (((((((((p5 → p5) ∧ p4) ∧ (False ∨ True)) ∨ (True → ((p2 ∧ p4) → p5))) → p1) ∨ (True ∨ p1)) ∧ p4) ∨ ((p4 → p2) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69358376689940943641939001652 : ((p5 → (p4 ∨ ((((p1 → p4) ∨ (((False ∧ ((p3 → ((p1 → (p2 → p3)) ∧ p4)) ∧ p5)) ∨ p3) ∨ p2)) ∧ p3) ∨ (False → True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175192389147158816047087551035 : ((False ∨ ((p4 ∨ ((False → (p1 → ((p3 ∧ p2) ∨ (False ∧ p2)))) ∧ p4)) ∨ False)) → (((False → p3) ∧ p5) → ((p2 ∨ (p3 ∨ p1)) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
    case inr h12 =>
      -- False on the left can always be used.
      apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149633259682625019496386339777 : ((p4 ∧ ((p1 ∨ (p5 ∨ (p1 ∧ ((((False ∧ (p5 ∧ False)) ∨ ((p3 ∨ p5) ∧ p3)) → p4) ∧ True)))) ∨ p1)) ∨ (((p5 ∧ p3) ∧ False) → p5)) := by
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
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159244266429252867961774200069 : ((p3 → ((p2 ∨ (p1 ∧ ((p1 ∨ (True ∨ p5)) ∧ p3))) ∧ (((p4 ∨ True) ∧ (p3 → True)) → p5))) ∨ (((p3 → (p5 ∨ p3)) ∧ True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695195788849444653821892438471 : (((((False ∨ ((((p4 ∧ True) ∧ ((p4 ∧ True) ∧ True)) ∨ False) → False)) ∨ True) → ((p2 ∧ ((p4 ∧ (p1 ∨ False)) → False)) → (p4 ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3991496678156202523843984203 : (p1 ∨ ((p5 ∧ (p5 → (False ∨ p2))) ∨ (((((p3 ∨ (True → p2)) ∨ (p4 ∧ False)) ∧ ((p1 ∨ True) → (False ∧ p5))) → False) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h6 : (p1 ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h7 := h3 h6
      -- We need to get the left conjuct of h7 based on <expert-advice>.
      let h8 := h7.left
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h10 : (p1 ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h11 := h3 h10
      -- We need to get the left conjuct of h11 based on <expert-advice>.
      let h12 := h11.left
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115083478543937332332661074345 : (((p5 ∧ (p1 → ((p2 ∧ ((p5 ∨ (False ∧ False)) ∧ p5)) ∨ False))) ∨ (((p5 ∨ p5) ∧ (p5 ∨ (False ∧ (p3 → p5)))) → p1)) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247391405456078914041859800861 : ((False ∨ p1) ∨ (p2 ∨ (((p4 → (((False ∧ p3) ∨ ((((True → p2) → (p3 ∨ p3)) → (True → p4)) ∨ p2)) ∨ (p5 ∧ p1))) ∨ p5) ∨ p5))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37134961448035301378823319045 : ((((((p2 ∧ p2) ∧ (((((p5 → p1) ∨ (True → p1)) → (False ∨ ((True ∧ p3) ∨ False))) ∧ True) ∧ True)) ∨ (p2 ∨ p1)) ∧ p2) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200582060655127970386066948531 : ((True ∧ ((p4 ∨ ((False ∨ p4) ∧ p1)) → p3)) → (((True ∧ ((False ∧ (p3 → p5)) ∨ p5)) ∧ p4) ∨ ((p4 ∨ p1) → (p1 ∨ (p5 ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352814780843625864643967622757 : (p4 → ((p5 ∨ p2) → ((((p2 ∧ ((((True → p2) → False) → ((p4 ∧ False) ∨ p2)) ∧ True)) ∧ p5) ∧ ((p5 → (p4 ∧ p4)) → p2)) ∨ p4))) := by
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
theorem thm_5_vars_60067878232849785106421456346 : (((p2 ∨ p2) → ((True → False) → (((p4 ∧ (((((p3 → p4) ∨ p1) ∧ (p2 ∨ p3)) ∧ p1) ∧ p4)) ∨ (p4 ∧ (p5 ∧ p3))) ∧ False))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h4
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h7
    -- False on the left can always be used.
    apply False.elim h8
  -- Disjunctions on the left can always be decomposed.
  cases h1
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616502659541466518422448413777 : (((((False ∨ (((((p3 → True) ∨ p3) ∧ False) ∧ (p5 ∨ p1)) ∨ True)) → (((p5 ∧ (p3 ∨ True)) ∧ p4) ∨ (p2 ∨ (p4 ∧ p4)))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63093058216335648736576808866 : ((p5 ∧ ((((p3 ∨ (p1 ∨ p2)) ∧ p5) → ((((p1 ∧ p1) ∧ p5) ∧ p1) ∨ (p2 → (True ∨ ((p2 ∧ p3) → (p5 ∨ p3)))))) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_195144533222572993678531677058 : (((True ∨ (True ∧ (True ∨ p1))) ∧ (p1 → True)) ∧ (True ∧ (((p4 ∨ p1) ∨ (p3 ∨ (False ∧ (p3 → p1)))) ∨ (p2 → ((p5 → False) → True))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153172745987199452455505414351 : ((p5 ∧ ((True ∨ (p2 → False)) → (p2 → ((((p3 → (p3 → p5)) ∨ (p2 → (p5 ∨ p2))) ∧ p4) ∧ True)))) → (((p3 ∨ True) → p3) → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : (p3 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h5
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178170354603719036456330230940 : ((((p2 ∧ p2) → (p3 ∨ ((p3 ∨ (p4 ∨ (p2 ∨ True))) → True))) → p3) ∨ (False ∨ ((False ∧ (((True ∨ False) → p5) ∧ p1)) → (p5 → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186106288450847945932773188034 : ((((p4 ∨ (p1 ∨ ((p3 ∨ True) ∧ p2))) ∨ (True ∨ True)) ∨ False) → ((True ∧ (p5 ∧ ((True ∧ p2) ∧ (p2 → (p2 → (p2 ∧ p1)))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h6 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h7 =>
          -- Conjunctions on the left can always be decomposed.
          let h8 := h7.left
          let h9 := h7.right
          -- Disjunctions on the left can always be decomposed.
          cases h8
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
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h15 =>
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250169604326726884337618742079 : ((True → p5) ∨ (((True ∧ True) ∨ False) ∧ ((True ∧ (p2 → ((True → p3) → (((p4 → False) → p4) ∧ False)))) ∨ ((True → False) → (p1 → p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219735334684501127336798487930 : ((p1 → (p5 ∨ (p3 → p1))) → (((p1 → True) → (p1 ∧ (False ∨ p3))) → ((p5 ∧ (((p5 ∨ (p4 ∧ p1)) → (p2 ∨ False)) → p4)) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p1 → True) := by
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
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134879482739648893542080016950 : (((p2 → (False → ((p3 → ((p1 ∨ (((p3 ∧ p4) ∧ (False ∧ (True → p4))) ∨ p5)) ∧ p5)) ∨ (False → False)))) → p1) ∨ (True ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37161024762532924705006679334 : (((((((p3 → (p5 → (((True ∨ p5) ∧ (p2 ∧ p3)) ∧ True))) ∧ (p3 ∧ True)) → p2) ∨ (False ∧ (p4 → (p1 ∨ p4)))) ∧ p3) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40187966992972135994607097231 : (((((True ∧ (p4 → p3)) ∧ (((p1 ∨ p3) ∨ (p2 → (p4 ∨ p3))) ∧ (p4 ∨ ((((p3 ∨ p1) ∧ p1) ∨ True) ∨ p5)))) ∧ p1) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351725962332731679305871642832 : (p4 → (((p1 → (((p2 ∨ p5) → (False ∧ p2)) ∧ (p1 → (p3 → p5)))) → p3) ∨ ((((p3 ∧ p1) ∧ p2) ∨ p3) → (p1 → (p3 → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41354207645133892809647443215 : ((((p5 → (((True ∨ (p1 ∨ (p5 ∧ True))) ∧ (p4 ∨ ((p3 ∨ p2) ∨ p3))) → p4)) ∨ (p2 → ((p3 → (p2 ∧ p4)) ∧ p5))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135942926310072288928716040905 : ((((p4 ∧ ((p3 ∨ p4) ∧ ((p2 ∨ p1) ∧ True))) → False) ∧ (True ∧ (p1 → (p3 → (p5 → (p2 ∨ (p5 ∨ False))))))) ∨ (p4 ∨ (p2 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328518315415197599176113464318 : (True → (((p2 ∨ ((p4 ∨ p4) ∨ ((p1 → (p4 ∧ (p3 → False))) ∨ True))) ∨ (p4 ∨ p4)) ∨ ((p2 ∧ p3) ∧ (True → (p4 ∨ (p1 → True)))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166958079178001786011202296350 : (((True ∧ (p2 ∧ (p1 → (((p3 ∧ (True ∧ p5)) ∧ p5) ∨ (p1 → (False ∧ p1)))))) ∧ p4) → (((((False ∧ False) ∧ p1) → p2) → p3) ∨ p2)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53650386552910412934954255306 : (((((p2 ∧ True) ∨ p4) → ((p1 ∨ p2) ∨ (True → p5))) ∧ (((p2 ∨ p4) → ((p4 → (p1 → ((p2 → True) ∧ False))) ∨ True)) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137989158417554676951806072524 : ((p5 ∨ (False ∧ ((True ∧ ((p3 ∧ (p5 → ((True ∧ (p3 ∧ (True ∨ p5))) ∧ (p5 ∧ p5)))) ∨ p5)) ∨ (p5 ∨ p5)))) ∨ (False → (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_781495677085665386680822163618 : (((p2 ∨ (p5 ∧ (p1 ∧ ((((p4 ∨ ((((p4 ∧ p4) ∧ (False ∧ (p1 ∨ p3))) ∨ (True → (p4 ∨ p1))) ∧ p2)) ∧ p5) → p4) ∧ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62603056902108224120343934545 : ((p3 ∧ (p5 → ((p4 ∧ (p4 ∧ (p4 ∧ (p5 ∨ p1)))) → (((p3 → (p1 ∧ p3)) ∧ ((p4 ∨ False) ∧ p3)) → ((False ∨ p2) ∨ p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136193182235270156710457646290 : ((((p4 ∧ p3) ∨ (p1 → (p3 ∨ False))) ∧ ((((p4 → p2) ∨ ((False ∧ p5) ∨ False)) ∧ p1) ∨ ((False ∨ p2) ∨ p1))) ∨ (p1 ∨ (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_725061304177175546442663445266 : ((((False → (p2 ∨ p5)) ∧ (((p3 ∧ ((p1 ∧ p1) ∧ (p4 ∨ (True → (((p2 ∧ (p5 ∧ p1)) ∨ (p4 ∧ p2)) ∧ p2))))) ∨ p1) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51639462778363956785682428217 : (((((False ∧ (((True ∧ p5) → p5) ∧ (False ∨ True))) ∨ (p2 ∧ (p3 ∧ p2))) ∨ True) ∧ (p5 ∨ ((((p4 ∨ p2) ∧ p1) ∧ p2) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3318261606453831478743438364 : ((p3 ∧ p4) → ((p5 ∨ True) → ((p5 → True) → ((((p1 ∨ p5) ∨ (p5 ∧ (True ∧ p2))) ∧ (p3 ∨ (False ∨ (p1 ∧ p2)))) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h1.left
    let h6 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h1.left
    let h9 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_71684668167314217145449162351 : (((p2 ∧ ((p2 ∧ (p3 ∨ (((((True ∨ (p5 ∨ p1)) ∧ p4) → (p5 ∨ (p1 ∨ False))) ∧ (True ∧ (p3 ∨ True))) ∨ p1))) → False)) ∧ p1) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : (p2 ∧ (p3 ∨ (((((True ∨ (p5 ∨ p1)) ∧ p4) → (p5 ∨ (p1 ∨ False))) ∧ (True ∧ (p3 ∨ True))) ∨ p1))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329044983711142633915202007367 : (True → ((True → ((p3 ∧ (p4 → p5)) → p5)) → (False ∨ (((p4 → ((False ∨ p1) ∨ (p2 ∨ p5))) ∨ (False → p1)) ∨ ((p5 ∨ p3) ∨ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323506145573588092129104815632 : (p5 ∨ ((((False ∧ p4) ∨ p2) ∧ (((True → ((False ∧ p2) ∧ (p3 → (p4 ∧ False)))) → (False → (False → False))) ∧ p2)) ∨ (True → (p4 → p4)))) := by
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
theorem thm_5_vars_136284942994534766736080692250 : ((((p3 ∨ True) → ((p5 ∨ p5) ∧ False)) → ((p5 ∧ (((p2 → ((p1 → p3) ∨ p3)) ∧ p2) → (p1 ∨ False))) ∨ p5)) ∨ ((p4 → p2) ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_942294359539943072537380256996 : ((((((p5 ∨ p2) ∨ p5) ∨ p1) ∧ ((((p2 ∧ p1) ∨ (False → p2)) ∨ (False ∧ (p5 → p5))) → ((False ∧ (p1 → p2)) ∧ (p4 ∧ p3)))) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      cases h5
      case inl h6 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h7 : (((p2 ∧ p1) ∨ (False → p2)) ∨ (False ∧ (p5 → p5))) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h8
          -- False on the left can always be used.
          apply False.elim h8
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h9 := h3 h7
        -- We need to get the right conjuct of h9 based on <expert-advice>.
        let h10 := h9.right
        -- We need to get the right conjuct of h10 based on <expert-advice>.
        let h11 := h10.right
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h12 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h13 : (((p2 ∧ p1) ∨ (False → p2)) ∨ (False ∧ (p5 → p5))) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h14
          -- False on the left can always be used.
          apply False.elim h14
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h15 := h3 h13
        -- We need to get the right conjuct of h15 based on <expert-advice>.
        let h16 := h15.right
        -- We need to get the right conjuct of h16 based on <expert-advice>.
        let h17 := h16.right
        -- One of the premise coincides with the conclusion.
        exact h17
    case inr h18 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h19 : (((p2 ∧ p1) ∨ (False → p2)) ∨ (False ∧ (p5 → p5))) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h20
        -- False on the left can always be used.
        apply False.elim h20
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h21 := h3 h19
      -- We need to get the right conjuct of h21 based on <expert-advice>.
      let h22 := h21.right
      -- We need to get the right conjuct of h22 based on <expert-advice>.
      let h23 := h22.right
      -- One of the premise coincides with the conclusion.
      exact h23
  case inr h24 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h25 : (((p2 ∧ p1) ∨ (False → p2)) ∨ (False ∧ (p5 → p5))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h26
      -- False on the left can always be used.
      apply False.elim h26
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h27 := h3 h25
    -- We need to get the right conjuct of h27 based on <expert-advice>.
    let h28 := h27.right
    -- We need to get the right conjuct of h28 based on <expert-advice>.
    let h29 := h28.right
    -- One of the premise coincides with the conclusion.
    exact h29
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727617204884649753171238599404 : ((((p5 ∧ (p5 ∨ p3)) ∨ (((p5 → (((p3 → p2) → ((p2 ∧ False) ∧ (True ∨ ((p4 → (True ∨ False)) ∧ False)))) ∧ True)) → p4) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171951318777805942885150661969 : (((((False ∧ (p1 ∧ p4)) → (p3 ∨ p4)) → (p2 ∧ (p1 → p4))) ∧ (p1 ∧ p5)) ∨ (p2 → ((p2 → p3) → ((p1 → (p3 → p5)) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55581381526945819650821473072 : (((p1 ∨ (p5 → ((p3 → True) → p5))) → (p4 ∧ (True → ((p3 ∨ (p4 ∧ ((False → p3) ∨ p1))) ∨ (p2 ∧ ((p1 ∨ p1) ∨ p3)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174637734496577689408921888794 : (((True → (p2 ∨ (False → p1))) → ((((p5 → (p5 ∧ p5)) ∧ p2) ∨ True) ∧ p1)) → (p2 ∨ ((p3 → ((True ∧ p2) ∧ (p5 → True))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165353019020124481994960437233 : (((p3 ∧ (((True ∧ (p2 → p1)) ∨ (p1 ∧ False)) → (False ∨ False))) ∧ (p4 ∧ (p4 → p3))) ∨ ((p4 ∧ (p5 ∨ ((p2 → p5) → p2))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53916035310198538430482258287 : (((p1 ∨ ((((p4 → p2) ∨ (False ∨ False)) ∨ p3) ∨ p5)) ∨ ((p3 → True) ∨ (True → ((p2 ∧ (True ∨ p5)) → ((False ∨ p2) → p3))))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115462178431590589391695930223 : (((p1 ∧ (((True ∧ True) ∧ (p3 ∧ p3)) ∨ p5)) ∨ ((p2 ∧ (p2 ∧ True)) ∧ ((p1 → True) → ((p5 → p5) ∧ (False ∨ False))))) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39329909903679168611438263047 : (((p2 ∧ ((p1 → (((p4 ∨ p1) ∧ (p1 → (False ∧ ((p3 ∨ p2) ∨ p5)))) ∨ (False ∨ p4))) ∨ (p5 → ((p2 ∧ p2) ∧ False)))) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307509374595393149567375812171 : (p1 ∨ (True → (((p2 ∨ p2) ∨ (((p1 ∧ p2) ∨ True) ∨ False)) ∨ ((p2 ∨ (((True → ((True ∨ p2) ∧ p1)) → (False → p2)) ∨ p4)) ∧ p3)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304739421036696826523529685544 : (p1 ∨ ((((p5 ∨ (p2 ∨ p2)) → p1) ∧ (((p5 → p4) ∨ (p3 ∨ (p1 ∧ ((p4 ∨ (p3 ∨ (p5 ∧ p4))) → p1)))) → p5)) ∨ (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



