variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_630922774862835144893579278434 : (((((((False ∧ p3) ∨ ((False → ((((False → ((((False ∨ False) ∧ p5) ∧ p1) → p1)) ∧ p1) → False) ∨ True)) ∧ p3)) ∧ False) → False) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39568470425643922739660373788 : (((p1 ∨ ((p2 ∧ (((p2 → (p1 ∨ True)) ∧ (p1 ∧ (p1 ∨ p1))) ∨ p2)) → ((((p4 ∨ p2) ∧ p5) ∨ True) ∧ (p1 → p2)))) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308349749550229270671371759889 : (p2 ∨ ((((False → ((p1 → p5) ∨ p2)) ∧ ((p1 → ((p4 ∨ p5) → (True ∧ (True → (((p3 → p1) ∧ p1) ∨ p1))))) → p1)) ∧ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136467000827816091105759334289 : ((((p3 ∧ p4) ∧ p2) ∧ (p3 → ((((p4 ∧ (((p1 ∨ False) ∧ p3) → p4)) ∨ (p1 ∧ True)) ∧ (p4 ∧ p3)) ∨ p5))) ∨ ((False ∧ True) → p5)) := by
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
theorem thm_5_vars_190879786217532145900343161758 : ((((p3 → p1) ∧ (p2 ∨ (p4 ∨ p5))) → (p2 ∧ p5)) ∨ (p1 → (((False ∨ False) ∧ ((p4 ∨ ((True → p2) → True)) ∧ (p5 ∨ p5))) → p3))) := by
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
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197699881696297664188979533946 : (((False → ((True ∨ p3) ∨ False)) → (p4 ∧ p3)) ∨ ((p3 ∨ (p2 → ((p3 ∧ p4) ∨ ((True ∨ p1) ∧ p2)))) ∨ ((True → p3) → (True → p4)))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225120438710078956923896254984 : (((p2 ∧ p4) ∧ p3) ∨ (((((((p4 ∨ p5) ∨ p5) ∧ True) ∨ True) → False) ∧ ((p3 ∧ p4) ∨ p2)) → ((p1 ∨ False) ∨ (p2 ∨ (True ∨ p4))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712965820163858497598308148104 : ((((p1 ∧ ((p4 ∧ p1) ∧ (p2 ∨ p1))) ∨ ((p5 → (False → (((p1 ∧ False) ∨ ((p3 → p3) ∨ ((p2 ∨ p1) ∧ p1))) ∨ p5))) ∨ p3)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160589135831098460395954055523 : ((((((p4 ∧ p4) → p3) ∧ (p4 ∧ (p5 ∧ p4))) ∨ p4) ∧ ((p2 → (False ∧ False)) ∧ (p2 ∧ p3))) → ((((p3 → p2) → p5) → False) ∧ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h4.left
    let h13 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h16 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h14
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h17 := h12 h16
    -- We need to get the left conjuct of h17 based on <expert-advice>.
    let h18 := h17.left
    -- False on the left can always be used.
    apply False.elim h18
  case inr h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h4.left
    let h21 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h22 := h21.left
    let h23 := h21.right
    -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
    have h24 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h22
    -- We have shown the premise of h20, we can now drive its conclusion.
    let h25 := h20 h24
    -- We need to get the left conjuct of h25 based on <expert-advice>.
    let h26 := h25.left
    -- False on the left can always be used.
    apply False.elim h26
  -- Conjunctions on the left can always be decomposed.
  let h27 := h1.left
  let h28 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h27
  case inl h29 =>
    -- Conjunctions on the left can always be decomposed.
    let h30 := h29.left
    let h31 := h29.right
    -- Conjunctions on the left can always be decomposed.
    let h32 := h31.left
    let h33 := h31.right
    -- Conjunctions on the left can always be decomposed.
    let h34 := h33.left
    let h35 := h33.right
    -- Conjunctions on the left can always be decomposed.
    let h36 := h28.left
    let h37 := h28.right
    -- Conjunctions on the left can always be decomposed.
    let h38 := h37.left
    let h39 := h37.right
    -- We want to use the implication h36 based on <expert-advice>. So we show its premise.
    have h40 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h38
    -- We have shown the premise of h36, we can now drive its conclusion.
    let h41 := h36 h40
    -- We need to get the left conjuct of h41 based on <expert-advice>.
    let h42 := h41.left
    -- False on the left can always be used.
    apply False.elim h42
  case inr h43 =>
    -- Conjunctions on the left can always be decomposed.
    let h44 := h28.left
    let h45 := h28.right
    -- Conjunctions on the left can always be decomposed.
    let h46 := h45.left
    let h47 := h45.right
    -- We want to use the implication h44 based on <expert-advice>. So we show its premise.
    have h48 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h46
    -- We have shown the premise of h44, we can now drive its conclusion.
    let h49 := h44 h48
    -- We need to get the left conjuct of h49 based on <expert-advice>.
    let h50 := h49.left
    -- False on the left can always be used.
    apply False.elim h50



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204227167833080324396062663596 : ((((False → (p5 → p3)) → False) ∧ p5) ∨ (p2 → (p2 ∨ ((((((p4 → (p5 ∧ p1)) ∨ p1) → p4) ∧ p1) ∧ (p4 ∨ p3)) ∧ (p2 → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161913818616341704758968919414 : ((p1 → ((((True ∧ p5) → (True → (p2 ∨ (p3 ∨ False)))) ∨ (True ∨ True)) ∨ ((p4 ∧ p1) ∨ p1))) → ((p1 → p3) ∨ ((True ∨ p4) ∨ p1))) := by
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
theorem thm_5_vars_344157689239082989067833597891 : (p2 → (False ∨ (p5 → (p2 → (p3 ∨ ((p4 ∨ (((p2 → p2) ∧ ((p5 ∨ False) ∨ ((True ∨ p3) → (p3 → (p5 ∧ p3))))) → p1)) ∨ True)))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167087097756899288421881430457 : ((((p5 ∨ (p5 → (p2 ∨ (((p4 → p4) ∧ ((p4 ∧ True) ∨ p3)) ∨ p5)))) → False) ∨ p2) → (((p1 ∧ p5) ∨ (p3 ∧ p5)) ∨ (False → True))) := by
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
theorem thm_5_vars_41775596774998750708430747067 : ((((p2 → (p2 → (p5 → p1))) ∨ (p1 ∨ (((True → p2) ∧ (p4 ∨ p2)) ∨ ((p3 → False) → (False ∨ ((p3 ∧ True) ∨ p1)))))) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64577945826129650987557317609 : ((p1 ∨ ((True ∨ (True → p5)) → (((((p3 → p1) ∨ (((p5 ∧ ((p3 ∨ p5) → p5)) ∧ p3) ∨ (p4 ∨ p4))) → p1) ∨ p3) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695408886672138806204149329364 : (((((p3 ∨ ((((p3 → p5) → False) → (p1 → p3)) → p5)) ∧ (p4 ∧ p5)) → (((((p3 → False) ∨ True) ∨ p4) → p2) ∨ (p4 ∨ p3))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h3.left
    let h9 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783757662027470596558962935471 : (((p3 ∨ (((p4 ∨ (p4 → p3)) ∨ p4) ∧ (p3 ∨ (((p3 → (p1 ∨ (p4 ∨ (p2 ∨ p5)))) ∨ (p1 ∧ (p2 → False))) ∧ (p5 ∧ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_733068574899142091599293842538 : ((((p3 ∧ True) ∧ ((((p4 ∨ (((False ∨ p4) → False) → (True ∨ (False ∧ p5)))) → (p3 ∧ p5)) → (False ∧ ((p4 → True) ∨ False))) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44966359806498773465779962607 : ((((p5 ∨ p5) ∧ (((p2 ∧ True) → p1) ∧ ((((((p5 ∨ p2) → (True ∨ p4)) → p4) ∧ p2) ∧ p3) ∨ ((p2 → p3) ∧ p1)))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135696493974914123848215091468 : (((((p4 ∧ True) ∧ (((p3 ∨ p5) ∧ p4) ∨ True)) ∨ ((False ∧ p1) ∧ p2)) ∧ (p4 ∧ (True ∨ (p4 → (True ∧ True))))) ∨ ((True → p1) → p1)) := by
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
theorem thm_5_vars_230866761987507010245468805077 : (((p1 ∧ p4) ∨ p2) → (False ∨ ((((((p3 ∧ p2) ∧ p5) → (True → ((False ∨ False) ∧ p5))) ∨ (False → (p4 ∨ True))) ∨ p3) ∨ (False ∨ True)))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264856023709378784766930241233 : (True ∧ ((p4 ∨ p5) ∨ ((False ∨ p4) ∨ (((p3 ∨ p2) ∨ True) ∨ ((p2 → ((((p2 ∨ (True → p1)) → p2) ∧ (True ∧ p3)) → p3)) ∨ p5))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_38374749015976302165338628617 : ((((p1 ∨ (p4 ∧ ((True ∨ ((False ∧ (p2 ∨ (False ∨ p5))) → (p4 ∨ p1))) ∧ False))) ∨ ((True → (p2 ∨ False)) ∧ (True → True))) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698946576136092266212343314138 : ((((p4 ∧ (p5 ∧ ((((p3 ∨ p2) ∧ (p2 → p1)) → True) → p3))) ∨ ((p3 ∧ p2) ∨ ((p5 → (False ∧ (p4 ∧ False))) ∧ (p3 → p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179780866775458028829838995630 : (((((p3 ∧ p3) ∧ p3) ∧ (p2 → (False → ((False ∨ p1) → p5)))) ∧ p5) → (((p2 ∧ ((p4 → p3) → p4)) ∧ (p2 → (p3 ∧ p5))) ∨ p3)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64374587535192804618707640927 : ((p1 ∨ ((False ∧ (p2 ∧ (((True ∨ p2) → ((p2 ∧ p1) ∧ p4)) ∨ ((((p1 ∧ p5) ∧ (p5 → (p4 ∧ p2))) ∧ p3) ∧ p3)))) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157162456438910585100674074174 : ((((p5 ∨ (((((p5 ∨ p3) ∨ (True ∨ p5)) ∨ p4) → (p1 ∧ (p3 ∨ False))) ∨ p5)) ∨ p2) → False) ∨ (p3 → (((True ∨ True) ∧ p1) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118289440855440371273137459246 : ((p1 ∨ ((p1 ∨ p4) → ((p3 → (((p2 → (p3 ∨ p4)) → p2) → (p5 → (p4 ∨ (p5 ∨ p2))))) → ((p2 ∨ True) ∧ p2)))) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191379533513842892209545504509 : (((p2 → p5) ∨ ((p3 ∧ p4) → (False ∧ (p3 → p2)))) ∨ ((p3 → (((p4 → (False ∨ (True ∧ p3))) → False) ∨ (p3 ∨ (p1 → True)))) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_646667381335676459119376672720 : ((((p1 → (p4 → ((((p2 ∧ (p4 ∧ ((p3 ∨ False) ∧ True))) ∨ ((p4 ∧ p3) ∧ p5)) → ((p5 ∨ p2) → p2)) ∧ (False ∨ p1)))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302696090386003112634639202434 : (False ∨ (p3 ∨ (((((p2 ∧ (p5 ∧ p4)) ∨ ((p2 → p4) ∨ (False ∨ ((p4 → True) ∨ p1)))) ∨ p3) ∨ False) ∧ (((p3 → p1) ∨ p2) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248755371480308774823835333820 : ((p3 ∨ p3) ∨ ((((p1 → ((p5 ∨ (p5 ∧ p2)) ∧ p3)) ∨ (p2 ∨ (p4 → False))) ∨ (p3 → ((True ∧ p4) ∨ (False ∨ p1)))) ∨ (True ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183813653177890649067796443865 : ((((((p5 → (p3 → p5)) → (True ∨ p3)) ∧ p4) → p1) ∧ False) ∨ ((((False ∧ ((p2 → False) → p3)) ∧ (False ∧ p1)) ∨ (p4 ∧ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248698389969936554219464230702 : ((p3 ∨ p2) ∨ (((p2 → (((p2 ∨ False) → (p3 ∨ (p3 ∧ True))) ∧ False)) → (((p1 → p4) ∧ (True → p1)) ∧ p2)) ∨ (p5 ∨ (p5 → True)))) := by
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
theorem thm_5_vars_301631678876782931290609936324 : (False ∨ ((p1 ∨ (True → p3)) → ((((p5 ∧ p4) ∧ False) ∧ False) ∨ ((p5 ∧ (p3 ∧ ((p2 ∧ (p4 ∨ p4)) → p3))) → ((p2 ∨ p1) → p5))))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h3.left
      let h7 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h3.left
      let h12 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- One of the premise coincides with the conclusion.
      exact h11
  case inr h15 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h16
    -- Implications on the right can always be decomposed.
    intro h17
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h16.left
      let h20 := h16.right
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- One of the premise coincides with the conclusion.
      exact h19
    case inr h23 =>
      -- Conjunctions on the left can always be decomposed.
      let h24 := h16.left
      let h25 := h16.right
      -- Conjunctions on the left can always be decomposed.
      let h26 := h25.left
      let h27 := h25.right
      -- One of the premise coincides with the conclusion.
      exact h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178793125741078222705348920107 : ((((p5 ∨ p3) ∧ True) ∨ ((p2 ∧ p1) ∧ ((False ∨ True) ∧ (p5 ∧ p1)))) ∨ (((((p5 ∧ p3) ∧ False) ∧ p2) → (p4 ∨ (False → p1))) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_266212218719370370356901198652 : (True ∧ (p4 → ((True → (p5 ∨ p1)) → (p3 → ((((False ∨ p2) → True) → (((p3 ∧ p2) → ((p2 ∨ (p5 ∨ True)) ∨ p4)) → p2)) ∨ p3))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198434973873647754757319322154 : ((p4 ∧ (True → (p2 ∧ ((True ∨ p2) → True)))) ∨ ((p2 → ((((p5 → (True ∨ p5)) ∧ p1) → p5) ∨ (p4 → True))) ∨ ((p4 ∧ True) ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60535908336659563713237737979 : ((True ∧ (((((((p3 → p1) ∨ p4) ∧ p4) ∨ p3) ∨ (p3 ∨ (((p3 ∧ True) ∧ p3) ∧ p5))) ∨ ((p4 → (p2 ∧ p3)) ∧ p4)) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2975595301244530589660091693 : ((p4 ∨ (p3 ∨ p4)) ∨ (((p1 ∧ (p5 → ((((p5 → (False → True)) ∨ p1) ∨ p4) ∧ p3))) ∨ (False → p2)) ∧ (p1 ∨ (True → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678492485875497723574072395698 : ((((((p2 ∧ p5) → True) ∧ (((True ∨ ((False ∨ p3) ∧ p3)) → (p2 ∨ ((p5 ∧ p1) ∨ p3))) ∨ p2)) ∨ ((p5 ∨ False) ∨ (p1 ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_994781787605003419099790131413 : (((p5 ∧ ((((p5 → (p5 ∨ p4)) → ((True → False) ∧ (p5 → (p1 ∨ (p5 ∨ True))))) ∧ ((True ∨ p4) ∨ p2)) ∧ ((True ∨ p2) → p5))) → False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  cases h7
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h10 : (p5 → (p5 ∨ p4)) := by
        -- Implications on the right can always be decomposed.
        intro h11
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h11
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h12 := h6 h10
      -- We need to get the left conjuct of h12 based on <expert-advice>.
      let h13 := h12.left
      -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
      have h14 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h13, we can now drive its conclusion.
      let h15 := h13 h14
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h17 : (p5 → (p5 ∨ p4)) := by
        -- Implications on the right can always be decomposed.
        intro h18
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h18
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h19 := h6 h17
      -- We need to get the left conjuct of h19 based on <expert-advice>.
      let h20 := h19.left
      -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
      have h21 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h20, we can now drive its conclusion.
      let h22 := h20 h21
      -- False on the left can always be used.
      apply False.elim h22
  case inr h23 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h24 : (p5 → (p5 ∨ p4)) := by
      -- Implications on the right can always be decomposed.
      intro h25
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h25
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h26 := h6 h24
    -- We need to get the left conjuct of h26 based on <expert-advice>.
    let h27 := h26.left
    -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
    have h28 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h27, we can now drive its conclusion.
    let h29 := h27 h28
    -- False on the left can always be used.
    apply False.elim h29
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117300066161680805774230827570 : ((False ∧ ((p5 ∧ ((p3 → (p2 ∨ (((False → False) ∨ p5) ∧ (((True ∧ p4) ∧ (p2 ∧ p5)) ∧ p1)))) ∨ True)) ∨ (False → p4))) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721734617266000578214025485238 : ((((p1 ∨ ((p4 → True) ∨ False)) → (((p1 ∨ ((((False ∧ p5) ∨ (True → (p1 ∨ ((False ∨ p1) → p5)))) ∨ p2) ∨ p3)) → p5) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51289606983313409228017288648 : (((p4 ∧ (((True → p2) ∨ (p1 ∧ ((((p2 ∧ p5) → p2) → False) ∧ p2))) ∨ (p3 ∨ p1))) ∨ (((p5 ∨ (p5 → p1)) ∨ p1) → True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704456170713730698312238171836 : ((((((False ∧ p4) ∨ p2) → (False ∧ ((p5 → False) ∧ p3))) → ((p3 → p3) → (p1 ∨ (((p5 ∧ (p1 → (True → p2))) ∧ p1) → False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67928367277841127577815527794 : ((p2 → ((p5 → (False ∨ ((p3 ∨ p1) ∧ (True → (p2 ∧ p1))))) → (((p1 ∨ (p2 ∧ (((True ∨ p4) → p1) ∨ True))) ∨ True) ∨ p1))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351517163797306909759473284411 : (p4 → ((((p2 ∧ (p2 ∨ p1)) ∨ (True → (p2 → (p2 ∧ (p1 ∨ (p3 ∨ (p5 ∨ False))))))) ∧ p3) ∨ (True → (((p1 ∨ False) ∧ p3) → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207148023589384856490767043041 : (((p1 → (False ∧ (p2 → True))) ∧ True) → ((((True ∨ (p5 → p5)) → p5) ∧ p1) → ((p4 ∧ p4) ∨ (((False → (True ∧ False)) ∨ p1) → False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h7 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h8 := h5 h7
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324000323586710106665286410691 : (p5 ∨ ((False ∧ (((((p3 → (p2 ∨ p3)) ∧ p2) ∧ True) ∧ (p4 → p3)) ∧ p2)) ∨ ((p5 ∧ p4) ∨ ((False ∨ (p2 ∨ (p3 ∨ p2))) → True)))) := by
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
theorem thm_5_vars_616175608129315319984105376001 : ((((((p5 ∧ (p1 → p1)) → (p1 ∨ (p4 ∨ ((False → p5) ∨ p4)))) ∧ (((((True → True) ∨ p5) → (p5 ∧ p3)) ∨ p2) ∨ True)) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_606677630980180370593208016938 : (((((((p3 ∨ (((p4 → p5) ∧ p1) ∧ (((p4 → p5) ∨ p1) → p1))) ∨ (p2 ∨ ((False → p1) → p2))) ∧ (p2 ∧ p3)) ∧ p4) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159333056336246695198295143205 : ((p5 → (p2 ∨ ((((p5 → p1) ∨ ((p2 ∧ (p4 → p2)) ∧ p5)) ∨ (p5 ∧ (p1 → False))) ∨ p3))) ∨ (p4 → (((False → True) ∧ p4) → p4))) := by
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
theorem thm_5_vars_117611363377887626222401762374 : ((p2 ∧ (p3 → ((p5 ∨ ((p4 ∨ (True ∨ (False ∧ True))) ∧ (((True → False) ∨ (True → p3)) ∨ (p2 → (p1 ∨ p5))))) → p2))) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322212729180420162527744618625 : (p5 ∨ (((((p5 ∧ ((((p3 ∧ False) ∧ p2) ∨ True) ∧ ((p4 ∧ (p5 ∧ p2)) ∨ p3))) ∧ False) ∨ (p3 ∧ (True → (p1 ∧ p2)))) ∧ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208370874953173505626517807909 : (((p1 ∧ p4) ∨ (p2 → (p1 ∨ p5))) → (((((p3 ∨ (False ∨ (p4 → p4))) ∨ p5) ∨ (p1 ∨ p1)) ∧ (p1 → (p5 ∨ (p1 → True)))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703680402297396443566770790828 : (((((((True ∨ ((True ∨ p4) ∧ False)) → True) → p3) ∧ p2) → (((p3 → p4) ∨ (p2 ∨ ((p1 ∧ False) → ((True → p1) → p4)))) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_587240570712791127177322482975 : (((((((((True ∨ p3) ∨ True) ∧ ((True ∧ p5) ∧ ((True ∧ ((True ∨ p4) → (p1 → (p4 → p5)))) ∧ p2))) ∨ p5) ∧ False) ∨ p4) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224983989513017775351467852906 : (((True ∧ p1) ∧ p1) ∨ (((False ∧ p3) ∨ True) ∧ ((p1 ∧ True) ∨ (True → (((False ∨ (p2 ∨ p5)) → ((p5 → p4) → (p3 → False))) → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_611896149732902795989163826590 : (((((p5 → (p4 ∧ (True ∨ (((p5 ∨ (p5 ∨ p2)) → (((((False ∨ p2) ∧ p5) → p1) ∨ p5) → (p4 ∧ p5))) ∧ p2)))) → p4) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38643580697963305838903633861 : (((((False → (((p1 ∧ p3) ∧ p4) ∧ p4)) ∧ p5) → ((((p5 → (p4 ∨ (False → (p4 ∨ True)))) ∧ (p1 → p1)) ∧ p4) ∧ True)) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809482371428854011917004828222 : (((p5 → (((((True ∧ p4) ∧ (((p5 ∨ p2) → (p1 ∨ ((p5 → p3) ∨ (True ∨ p5)))) ∧ (p1 ∧ p4))) ∨ False) → (p5 → p1)) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_804652018938972366212832593322 : (((p3 → ((((False ∨ p4) ∨ p5) → False) → ((p5 ∨ (((p2 ∧ (((p5 → (True → p3)) ∧ p1) → True)) ∨ p2) ∨ (p1 ∧ p4))) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119549650573692178169873674794 : ((p5 → ((((((False → False) ∧ p5) ∧ p1) → ((p5 → (p1 ∧ (p4 → p1))) ∨ (True → p3))) → p4) ∨ ((p3 ∨ p4) ∧ p5))) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48367872520709440500023636141 : (((p5 ∨ ((p2 → ((False → ((((p2 ∨ (((p1 ∧ p4) → False) → False)) → p4) ∨ (p4 ∧ p2)) ∨ p4)) → p4)) → p5)) → (p4 ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609674349306561687086243545597 : (((((p1 ∨ (((((p5 ∨ (p5 ∨ False)) ∨ p3) ∨ (((p5 ∧ True) → False) → p3)) ∧ (p2 ∨ p2)) → (False ∨ (p1 ∨ p2)))) ∨ True) ∨ False) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_59019298546850459582054659873 : (((p3 ∧ p5) ∨ (((p3 ∨ ((p1 ∧ p3) → (True ∧ (p4 ∧ p1)))) ∨ (((p2 → p3) ∧ (p4 ∨ (p4 ∨ p2))) ∧ (False → p4))) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610738091273891988501936816387 : ((((((((p1 ∨ (p4 ∨ (p2 ∨ True))) ∨ p4) ∧ (False → (p2 ∨ ((False ∧ (p1 ∧ p4)) ∧ p2)))) → (p5 → (p5 ∧ p4))) → p5) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53144638990718769498369110921 : ((((p4 → (((p4 ∧ ((p4 ∧ p1) ∧ p4)) ∧ p2) → p3)) ∧ p5) ∨ (p2 ∧ ((p4 ∧ ((p4 → (p3 → (p3 → p4))) → p5)) → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43609944336415002015019336850 : (((((((p4 → p1) ∨ ((p3 ∧ p1) → ((((p2 ∨ p2) ∨ p2) ∨ True) → (p4 → p1)))) ∨ (p5 → (p4 ∨ p3))) → p1) → False) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_335857835399904585556181267352 : (p1 → ((((p4 ∨ p2) ∨ ((p4 → ((p1 ∧ p3) → p2)) → False)) ∨ ((((p4 → True) ∨ p2) ∧ (True → p3)) ∨ ((p1 ∨ p5) ∨ p2))) ∧ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340949238048953030354152857604 : (p2 → (((False → (p4 ∨ p3)) ∧ ((((p4 → (p5 → p1)) → (False ∨ (p5 → False))) → (((p4 ∧ False) → True) ∧ (p5 ∨ p1))) ∨ p2)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113441224093921420693369773871 : ((((((p4 ∨ p3) → (True → False)) ∨ ((((((True → False) ∨ p1) ∨ (p5 → p3)) ∧ False) ∨ p3) ∧ False)) ∨ True) ∨ (p4 ∨ p4)) ∨ (p1 → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135628844257816187604852966549 : ((((p5 → (p2 ∧ (((((p2 ∧ p4) → p3) ∧ p1) ∨ p3) ∧ (True → p5)))) ∧ p3) → (p5 ∧ ((p1 ∧ p1) ∧ p4))) ∨ ((p2 ∧ p3) → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_385695162047401876185418461251 : ((((((False ∧ (p1 ∨ p2)) ∧ (((p5 → False) ∨ p3) ∧ (p5 ∨ (p1 ∧ ((p3 ∧ p4) → ((p4 ∨ p4) ∨ False)))))) ∧ (True ∧ False)) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_320539273294321507527844950331 : (p4 ∨ (True ∧ ((True → False) → ((p3 → True) → (p1 ∨ ((p1 → (p3 ∧ (p4 ∧ p4))) ∨ ((False ∧ p2) ∧ (p1 ∧ (False ∧ (p3 ∧ p4)))))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_113736428058479942487967424575 : (((((((p1 ∨ ((p1 ∨ ((True ∧ p2) → True)) → True)) ∧ True) → p5) ∨ p1) ∨ (True ∧ ((p3 ∨ p3) ∧ p5))) → (p2 ∧ p4)) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50121015901014380276904483930 : (((p2 ∨ ((True → ((p4 ∨ False) ∧ (((True ∧ p1) → ((False → p3) ∨ True)) ∧ (False ∧ p4)))) → False)) ∧ (p2 → (p5 ∨ (p4 → p2)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h8
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114595433523957193064535946339 : ((((p5 ∨ p2) → (p2 ∧ (((p4 → p5) ∨ ((False → p1) ∧ (p3 ∧ p4))) ∧ p2))) ∧ ((p5 ∧ (False → p1)) ∧ (p4 ∧ False))) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206364378194323126227894928652 : ((p2 ∨ (False ∧ (p1 ∨ (p5 ∧ p3)))) ∨ (((p4 ∧ ((((True → p4) ∧ (p1 ∨ True)) ∧ p4) ∨ (False → True))) → (p2 → (p5 ∨ p2))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_717353837428051840659955215799 : ((((p5 ∨ (True → (p4 → True))) ∧ (p2 → (p5 ∨ ((True → (p4 ∧ True)) ∧ ((p2 ∧ (((p5 ∧ p3) → False) ∧ False)) ∧ (True ∧ p2)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_195767820220613416154014951560 : (((True ∧ False) → (p4 → ((p1 ∨ p5) ∧ p4))) ∧ ((False ∧ ((p5 ∨ (True → p2)) ∧ (p5 → (((False ∧ (True ∧ p2)) ∨ p3) ∨ False)))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- False on the left can always be used.
  apply False.elim h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147370854980487725657793783999 : (((((p4 ∨ False) ∨ ((p2 ∧ p4) → (p1 ∨ (False ∨ (p3 ∧ False))))) ∨ (False → (True → (p5 → p2)))) ∨ False) ∨ ((p2 ∧ True) ∧ (p4 → False))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219539659849978832545899303366 : ((p5 ∨ (False → (p4 ∨ p2))) → ((((p3 → (True ∨ (p3 ∨ True))) ∨ p2) ∧ ((False → p2) → p5)) ∨ (False → ((p1 → p5) ∨ (p4 → p3))))) := by
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
theorem thm_5_vars_116183428065552110411385502982 : (((p4 → (False → p3)) ∧ ((((False → False) → p5) → False) → ((p4 ∧ (p2 → True)) → ((p5 ∧ True) → ((p1 → False) ∧ p2))))) ∨ (p4 → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h4.left
  let h10 := h4.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h11 : ((False → False) → p5) := by
    -- Implications on the right can always be decomposed.
    intro h12
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h13 := h3 h11
  -- False on the left can always be used.
  apply False.elim h13
  -- Conjunctions on the left can always be decomposed.
  let h14 := h5.left
  let h15 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h16 := h4.left
  let h17 := h4.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h18 : ((False → False) → p5) := by
    -- Implications on the right can always be decomposed.
    intro h19
    -- One of the premise coincides with the conclusion.
    exact h14
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h20 := h3 h18
  -- False on the left can always be used.
  apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159970216169400931832549397677 : (((((p5 → (p3 ∧ ((p3 → p2) ∧ (False ∨ (True → True))))) → p2) → (True ∧ (p2 ∨ p5))) → p5) → ((p4 ∧ (p4 ∧ (False ∨ p3))) → p3)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256393969919319603141897745416 : ((False ∨ p3) → ((((((p5 → (p4 ∨ ((p4 ∧ (p5 → (p3 → True))) ∨ (p1 ∧ False)))) ∨ p1) → False) ∨ (p4 ∨ (p1 ∧ p4))) ∧ p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207781140105650319176495181071 : (((p5 ∨ ((False ∧ False) ∨ p1)) → False) → (p1 → ((p1 → (True → (p1 ∨ (False ∧ True)))) ∧ ((p3 ∧ ((p1 ∨ (True → True)) ∧ p3)) ∧ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : (p5 ∨ ((False ∧ False) ∨ p1)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : (p5 ∨ ((False ∧ False) ∨ p1)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h7
  -- False on the left can always be used.
  apply False.elim h8
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h9 : (p5 ∨ ((False ∧ False) ∨ p1)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h9
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323718299008156826120254843457 : (p5 ∨ ((((p3 ∧ (False ∧ p5)) ∨ p3) ∧ (p5 → ((False → (p5 ∧ (True ∧ (p2 ∧ (p4 → True))))) ∨ True))) → (p4 ∨ ((True → False) ∨ p3)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213987022177046572522679015402 : (((p5 → (False ∨ p4)) ∨ p2) ∨ (True → ((p4 → ((((True ∨ p4) ∧ p1) ∨ (False ∨ (((False ∧ p4) ∧ p3) ∧ p4))) ∧ False)) ∨ (p3 → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317808214972930691832734585366 : (p4 ∨ (((((p1 ∧ False) ∨ (p4 ∨ True)) ∧ False) ∨ (((p4 ∧ ((p3 → (p2 ∨ p5)) ∧ p3)) → (p2 ∨ (False → (p4 ∧ p3)))) ∧ p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_918352222449606547670633918688 : ((((p5 ∨ ((p5 → ((False ∨ p3) → p5)) → (p1 → (((p1 → p2) ∨ p2) → p2)))) → (False ∧ ((p2 → (False → (p5 → p2))) → p2))) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 ∨ ((p5 → ((False ∨ p3) → p5)) → (p1 → (((p1 → p2) ∨ p2) → p2)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h7 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h8 := h6 h7
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h9
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h2
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- False on the left can always be used.
  apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158268391647791296365713330075 : (((False ∨ (p2 ∧ p5)) ∨ (p2 ∧ (p5 → ((p5 → False) ∧ ((p2 ∨ (p3 ∧ (p5 ∧ False))) ∧ False))))) ∨ (p4 ∨ ((p4 ∨ (p4 → True)) ∨ p5))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219508316734572207481311640356 : ((p5 ∨ ((False ∨ True) → p2)) → ((((p3 ∧ ((p3 ∧ (False ∨ (p4 ∧ p3))) ∨ ((True ∨ p3) → False))) ∨ (p5 ∨ p2)) ∧ (False ∧ False)) ∨ True)) := by
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
theorem thm_5_vars_51887287121410056031489599646 : ((((((p1 ∧ True) → (True ∧ ((False → (True ∨ p3)) ∧ p3))) ∨ (True → p2)) → p2) ∨ ((True → False) ∨ (p2 ∨ (p4 ∨ (True ∨ True))))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_115303749129350888471317624623 : ((((p3 ∧ ((p1 ∨ (p5 ∨ (p2 ∧ p4))) ∧ p2)) → p4) → ((False ∧ p3) ∨ (p2 ∨ (p5 → (((p1 → p2) → p1) ∨ p2))))) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780521857097569940171530603031 : (((p2 ∨ ((p3 ∧ (p4 ∨ (((p5 → (p1 → True)) ∨ (False ∨ p5)) ∨ p2))) ∧ ((p4 ∧ p2) ∧ (p2 ∨ ((False ∧ (p3 → p2)) ∨ p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165399021703004983560140489337 : (((True → (((p3 ∧ (True ∨ p2)) → p1) ∨ ((p4 ∨ False) ∨ p4))) ∨ (p1 ∧ (p4 ∧ p1))) ∨ ((True ∧ p4) ∨ (p3 → ((p3 ∧ p3) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165661563536583318286137468752 : ((((p2 → p4) ∨ (p4 → (p3 ∨ p2))) ∨ (p3 ∨ (((p4 ∧ (p5 ∧ p3)) → False) ∨ True))) ∨ (((True ∨ True) → True) ∧ ((False → p3) ∨ p2))) := by
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
theorem thm_5_vars_40035119444732382100561639861 : (((((((p5 ∧ p4) ∧ (((p1 ∨ True) ∧ p3) ∨ False)) → (p2 → (((p3 → False) ∧ p2) ∧ (p5 ∧ (p1 ∧ p5))))) ∧ p5) ∧ p4) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



