variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_700153774043094216292202609917 : (((((False → p5) ∧ ((p1 → (p5 ∧ (p5 ∧ (p2 ∧ p2)))) → True)) → (((p2 → p4) → (p5 ∧ p3)) ∧ ((p1 ∨ (True ∧ p4)) ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37150532747792094808060848132 : ((((((((False ∨ True) → p5) ∨ (((p5 → ((p3 ∨ True) ∧ False)) ∨ p2) ∧ p3)) → (True ∧ p4)) ∨ ((p1 ∧ p1) ∧ p5)) ∧ p3) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205666219034225259391999451954 : (((p1 ∨ p3) ∨ (False ∨ (p2 ∨ p3))) ∨ ((p1 ∨ ((((((p1 ∨ True) → (False ∨ True)) ∧ p5) ∨ (p2 → p4)) → p1) → (p1 ∨ p3))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309386914462910665989594850948 : (p2 ∨ ((p3 ∧ ((((p2 ∧ (p4 → p4)) ∨ p4) → (p3 ∧ ((((p3 ∨ False) ∨ (p3 ∧ p1)) ∨ p2) ∨ (False → p1)))) ∧ p5)) ∨ (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_887712009680206028754355630795 : (((((((((((p4 → p1) → p3) ∨ False) → False) ∨ ((p4 ∧ p1) ∧ False)) → p3) → (p3 ∧ (True ∨ p5))) ∨ (p3 → p3)) → (p4 ∧ p1)) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((((((p4 → p1) → p3) ∨ False) → False) ∨ ((p4 ∧ p1) ∧ False)) → p3) → (p3 ∧ (True ∨ p5))) ∨ (p3 → p3)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158194577177217377621762350249 : ((((p3 ∧ p4) ∧ p3) ∧ ((((p5 ∨ ((p1 ∧ (True ∧ p1)) ∧ p3)) ∧ p1) ∨ p3) → (p2 ∧ False))) ∨ (p1 ∨ (p3 → ((True ∨ p3) ∨ p3)))) := by
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
theorem thm_5_vars_136634518246186842569507872050 : ((((True → False) ∨ True) → ((((p1 → p2) → (p1 ∧ p1)) ∧ p5) ∨ ((p1 → p4) ∨ (True ∨ ((False ∨ p5) ∨ p5))))) ∨ (p1 → (p5 ∧ p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_15854425841490864500461516921 : ((((False → p2) → (((p1 → (p2 → (p5 ∧ True))) ∧ ((p1 → (p1 → ((p5 ∧ p5) → False))) ∨ (p5 ∧ True))) ∧ False)) → (False ∨ p3)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → p2) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656314910236196642039277535510 : (((((((((False ∨ p2) → False) ∧ p1) → p3) → ((p3 ∧ p3) ∨ p3)) ∨ (False → ((p3 ∧ ((p4 ∧ p2) ∧ False)) → p1))) ∨ (p3 → True)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_205497614245442029729984437985 : (((p2 ∧ p3) ∧ ((p1 ∨ p2) ∨ False)) ∨ (p2 → ((((((p2 → ((p5 → p1) ∨ p2)) ∨ p3) ∧ p2) → ((p2 → False) ∧ p3)) ∨ p2) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37202536410757248906630383226 : ((((((p3 ∨ False) ∨ (p4 ∧ p4)) ∧ (p3 ∧ (p4 → ((p2 → (p3 ∨ False)) ∨ (False ∧ ((p4 ∨ (p5 ∨ p3)) ∧ p5)))))) ∧ False) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44822776335673600047047459307 : ((((p1 → (True ∧ p4)) ∧ ((p4 → p2) → (((((p3 → (p2 ∧ p1)) ∧ (p2 ∧ (p3 ∧ p5))) ∧ (False ∨ p2)) → p4) ∧ p5))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45957906891859955865424992244 : (((p5 → (((p1 ∨ p1) ∧ p2) ∨ (p4 → (((((p1 ∨ False) ∧ p1) ∧ True) → (True → (False ∧ (False ∧ (p2 ∨ p3))))) ∧ p2)))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152400279650708378576828173969 : ((((True ∨ p3) ∨ (p5 ∧ True)) → (((p5 ∨ False) → (p1 → ((p4 → p2) ∨ (p5 ∨ (False ∨ p3))))) ∧ True)) → ((p4 → False) ∨ (p4 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118574565557017175636971543344 : ((p4 ∨ (((((((p2 → (((p3 → False) ∨ p5) ∧ p4)) → p1) ∧ p3) ∨ (True → p1)) ∧ (p2 → False)) ∧ (True → p5)) ∨ p2)) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221126435169510118867246482039 : (((True ∨ p1) ∨ p1) ∧ (((((p2 → (p3 ∧ (p4 ∧ p1))) → (p2 ∧ p4)) → False) ∧ p2) → (((((False ∧ False) ∧ p3) ∧ p3) ∧ p3) ∧ p2))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p2 → (p3 ∧ (p4 ∧ p1))) → (p2 ∧ p4)) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h3
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h7 := h5 h6
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- We need to get the left conjuct of h8 based on <expert-advice>.
    let h9 := h8.left
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h10 := h2 h4
  -- False on the left can always be used.
  apply False.elim h10
  -- Conjunctions on the left can always be decomposed.
  let h11 := h1.left
  let h12 := h1.right
  -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
  have h13 : ((p2 → (p3 ∧ (p4 ∧ p1))) → (p2 ∧ p4)) := by
    -- Implications on the right can always be decomposed.
    intro h14
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h12
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h15 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h12
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h16 := h14 h15
    -- We need to get the right conjuct of h16 based on <expert-advice>.
    let h17 := h16.right
    -- We need to get the left conjuct of h17 based on <expert-advice>.
    let h18 := h17.left
    -- One of the premise coincides with the conclusion.
    exact h18
  -- We have shown the premise of h11, we can now drive its conclusion.
  let h19 := h11 h13
  -- False on the left can always be used.
  apply False.elim h19
  -- Conjunctions on the left can always be decomposed.
  let h20 := h1.left
  let h21 := h1.right
  -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
  have h22 : ((p2 → (p3 ∧ (p4 ∧ p1))) → (p2 ∧ p4)) := by
    -- Implications on the right can always be decomposed.
    intro h23
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h21
    -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
    have h24 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h21
    -- We have shown the premise of h23, we can now drive its conclusion.
    let h25 := h23 h24
    -- We need to get the right conjuct of h25 based on <expert-advice>.
    let h26 := h25.right
    -- We need to get the left conjuct of h26 based on <expert-advice>.
    let h27 := h26.left
    -- One of the premise coincides with the conclusion.
    exact h27
  -- We have shown the premise of h20, we can now drive its conclusion.
  let h28 := h20 h22
  -- False on the left can always be used.
  apply False.elim h28
  -- Conjunctions on the left can always be decomposed.
  let h29 := h1.left
  let h30 := h1.right
  -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
  have h31 : ((p2 → (p3 ∧ (p4 ∧ p1))) → (p2 ∧ p4)) := by
    -- Implications on the right can always be decomposed.
    intro h32
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h30
    -- We want to use the implication h32 based on <expert-advice>. So we show its premise.
    have h33 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h30
    -- We have shown the premise of h32, we can now drive its conclusion.
    let h34 := h32 h33
    -- We need to get the right conjuct of h34 based on <expert-advice>.
    let h35 := h34.right
    -- We need to get the left conjuct of h35 based on <expert-advice>.
    let h36 := h35.left
    -- One of the premise coincides with the conclusion.
    exact h36
  -- We have shown the premise of h29, we can now drive its conclusion.
  let h37 := h29 h31
  -- False on the left can always be used.
  apply False.elim h37
  -- Conjunctions on the left can always be decomposed.
  let h38 := h1.left
  let h39 := h1.right
  -- We want to use the implication h38 based on <expert-advice>. So we show its premise.
  have h40 : ((p2 → (p3 ∧ (p4 ∧ p1))) → (p2 ∧ p4)) := by
    -- Implications on the right can always be decomposed.
    intro h41
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h39
    -- We want to use the implication h41 based on <expert-advice>. So we show its premise.
    have h42 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h39
    -- We have shown the premise of h41, we can now drive its conclusion.
    let h43 := h41 h42
    -- We need to get the right conjuct of h43 based on <expert-advice>.
    let h44 := h43.right
    -- We need to get the left conjuct of h44 based on <expert-advice>.
    let h45 := h44.left
    -- One of the premise coincides with the conclusion.
    exact h45
  -- We have shown the premise of h38, we can now drive its conclusion.
  let h46 := h38 h40
  -- False on the left can always be used.
  apply False.elim h46
  -- Conjunctions on the left can always be decomposed.
  let h47 := h1.left
  let h48 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h48



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47192979048404855079549178470 : (((((p1 ∧ ((True ∨ (p5 ∨ True)) ∨ p5)) ∨ ((p3 ∨ p4) ∨ p2)) ∨ (p3 → ((p5 ∧ (False ∧ (p2 ∨ p5))) ∨ p1))) ∨ (p3 ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53149077550994999029737483025 : (((((p3 ∧ ((False ∨ p3) → ((p5 → p4) → p1))) ∨ p3) ∨ False) ∨ (True ∨ (False ∨ ((True → (True → p3)) → (p3 ∧ (False ∧ p5)))))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_587798487876110625363490989958 : ((((((p4 ∨ ((((p2 ∧ ((((p3 ∧ (p4 ∨ (True ∨ p4))) ∨ p3) → True) ∨ p1)) ∧ p2) ∧ p2) → p2)) ∧ (p5 ∧ p1)) ∨ False) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310963826500693914372935353800 : (p2 ∨ ((p4 ∨ True) ∧ (p3 → (p4 ∨ (((p5 ∧ p4) ∧ (((p1 → ((p2 ∨ (p5 ∨ False)) ∨ p2)) ∧ (True ∧ (False → p5))) ∧ False)) ∨ p3))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601032427151153661448863910489 : ((((p1 ∧ ((p5 ∨ (p3 → ((p3 → p1) → p4))) ∨ (((p3 ∨ p4) → False) ∨ ((p1 ∨ (True ∧ p5)) ∨ ((p4 ∧ p2) ∧ True))))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313267065466086301701329909564 : (p3 ∨ ((False ∧ (False ∧ ((((p4 → (p2 ∧ False)) ∧ False) ∨ p4) ∨ ((p2 → True) ∨ ((p1 → (((p1 ∨ False) ∧ p2) → p4)) ∨ p3))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709327884547530227642668241278 : (((((p5 ∨ True) → (p5 ∨ ((p5 ∧ p5) → p5))) → (((p3 → (p5 → (False → (((False ∧ p2) ∨ (p3 ∧ p4)) → p4)))) → p4) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_931949675939269350753159733586 : (((((p5 ∧ ((p2 ∨ p5) → (p3 ∧ p5))) ∨ True) ∧ ((p2 ∨ (((False ∨ (p1 ∨ True)) ∧ (p1 → (False → p1))) ∨ p1)) → (True ∧ p1))) → p1) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h7 : (p2 ∨ (((False ∨ (p1 ∨ True)) ∧ (p1 → (False → p1))) ∨ p1)) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h8
      -- Implications on the right can always be decomposed.
      intro h9
      -- False on the left can always be used.
      apply False.elim h9
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h10 := h3 h7
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h13 : (p2 ∨ (((False ∨ (p1 ∨ True)) ∧ (p1 → (False → p1))) ∨ p1)) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h14
      -- Implications on the right can always be decomposed.
      intro h15
      -- False on the left can always be used.
      apply False.elim h15
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h16 := h3 h13
    -- We need to get the right conjuct of h16 based on <expert-advice>.
    let h17 := h16.right
    -- One of the premise coincides with the conclusion.
    exact h17
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134274892433866110404044181244 : ((((p4 ∨ p1) ∧ ((p3 ∨ ((True ∧ True) → (p1 ∨ p5))) ∧ ((True ∧ (p1 ∧ ((p3 → False) → True))) ∨ False))) ∨ p2) ∨ ((p1 ∨ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777682691750968561910750062056 : (((p1 ∨ (((p5 ∧ ((p5 → (p4 ∧ True)) → p2)) ∨ p4) ∨ ((p4 → ((p3 ∨ (((False ∧ p3) → (p3 → p2)) ∨ p4)) ∨ p2)) ∨ p5))) ∨ p5) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_734960484664073058174493196256 : ((((p2 ∨ p5) ∧ (((((p2 ∨ ((False → (p5 ∧ True)) ∨ ((p2 ∨ (p5 ∨ True)) ∨ True))) → True) ∧ ((True → True) ∧ p1)) ∨ p1) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183076994960227708801147835781 : (((False ∧ p5) → (((p1 ∧ p3) ∧ (p4 → (p3 → p4))) → p3)) ∧ ((((p5 ∧ (p4 ∨ p3)) → (p1 ∧ False)) ∨ (p4 ∨ p2)) ∨ (p2 → p2))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  let h7 := h1.left
  let h8 := h1.right
  -- False on the left can always be used.
  apply False.elim h7
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h9
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136831336487212470925211577943 : (((False ∧ p5) ∨ (((p2 ∧ p2) ∧ False) ∨ (p4 ∨ ((False → (((p3 ∧ p2) ∨ True) ∨ p1)) → ((True ∧ p4) ∧ p1))))) ∨ (p2 ∨ (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_889879152861861109102940078000 : (((((p4 → p1) ∨ ((p5 ∨ False) ∨ (((p5 ∧ p1) ∨ (False ∧ (p3 ∨ p1))) → ((((p1 → False) ∨ True) ∨ p4) ∨ False)))) → (p4 ∧ p3)) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p4 → p1) ∨ ((p5 ∨ False) ∨ (((p5 ∧ p1) ∨ (False ∧ (p3 ∨ p1))) → ((((p1 → False) ∨ True) ∨ p4) ∨ False)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- False on the left can always be used.
      apply False.elim h8
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h2
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- One of the premise coincides with the conclusion.
  exact h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149666862762766135838631217934 : ((p4 ∧ (p5 ∨ ((((((p4 ∨ ((p1 ∧ p4) ∧ (p3 ∨ True))) ∨ p3) ∧ p3) ∧ False) ∨ p1) ∧ (p4 → p3)))) ∨ (p1 → ((True ∧ p1) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57319773674519496083639701796 : (((False ∧ (p4 ∧ p2)) ∨ ((p1 ∨ p4) → (p2 ∨ (False ∧ (p1 ∧ (p1 ∨ (p2 ∧ ((((p1 ∧ False) ∨ (p4 ∨ p5)) ∧ p4) ∧ p1)))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356626373878946511740189286847 : (p5 → ((((p3 ∧ p5) ∨ p2) ∨ (p4 ∨ (p4 ∧ p2))) ∨ ((((True ∧ p4) ∨ False) → ((((False → p1) ∨ False) → (p1 ∧ p4)) → p1)) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355870749268133729403045179298 : (p5 → (((p3 ∧ p1) ∧ (((((((p5 ∨ p2) ∧ (p5 → True)) ∧ p5) ∧ p1) ∧ p5) ∨ p2) ∨ ((p3 ∨ p4) ∧ p3))) ∨ ((p1 → p3) → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263374961036365458168387352542 : (True ∧ ((((((p4 ∨ (((p1 → p1) ∨ p4) ∨ (p1 ∧ ((p3 → False) ∧ p4)))) ∨ p5) → (p2 → p2)) → p1) ∨ True) ∨ (p1 → (False ∨ p2)))) := by
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
theorem thm_5_vars_52522393117791881942776903673 : (((((p1 → (True → (True ∨ ((p5 → p2) ∨ (p4 ∧ True))))) ∧ p2) ∨ p2) ∨ ((p3 → ((p2 → (p1 → p3)) → True)) → (p5 → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64129453118526636989435765629 : ((False ∨ (((p2 ∨ p5) ∨ (p5 ∨ p3)) ∨ ((True ∧ True) ∨ (p5 ∧ ((p4 ∧ (((p4 ∧ p4) ∧ (False → p1)) → p1)) → (True → True)))))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217346920385639834853427527107 : (((p2 ∨ (p4 ∧ p4)) ∨ False) → ((((True ∨ (False ∨ (((p1 ∧ (p3 → ((p2 ∧ p1) ∧ p3))) → p4) ∨ False))) → p5) ∨ True) ∨ (False ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178088987766243086467383784068 : (((((True ∧ False) ∨ ((p2 ∨ True) ∧ (False ∧ (p1 ∧ p1)))) → p2) → p3) ∨ ((p3 ∨ ((p4 ∧ p3) ∧ p1)) → ((False ∨ p3) ∨ (p2 → p5)))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112846056033435227240262726663 : (((((p3 ∧ p5) → p5) ∧ (True → (((((((p5 ∧ p3) → p2) ∧ p1) ∧ False) ∨ p5) ∨ (p3 ∧ (p5 ∨ p5))) → p2))) → p4) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165343386403463461990645416730 : (((((p5 ∧ (p5 ∨ p2)) → p4) → ((p4 → (p4 ∨ p3)) → p3)) ∧ ((p3 ∧ False) ∧ p3)) ∨ ((((p5 ∧ (p2 → p4)) ∧ False) → p2) ∨ False)) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337428460780925830951407272871 : (p1 → ((((((p4 ∨ (p4 ∨ p3)) ∨ p1) ∧ ((p3 → p5) ∨ ((p1 → p2) ∧ False))) ∨ p4) → (False → (p1 ∨ p1))) → ((False ∨ p5) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_700857849593955185198462357248 : (((((((((p4 ∨ p1) → p2) ∧ p3) ∨ p2) ∧ p2) ∨ p1) ∧ ((p2 → False) ∨ ((True ∧ (True → (p1 ∨ p2))) ∧ ((True ∧ True) → p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344302157881964530448612914136 : (p2 → (p3 ∨ (((False ∧ ((p3 ∧ p2) ∨ p2)) ∧ ((((p1 → True) → (True ∨ p5)) → False) ∧ ((True → p5) ∧ False))) ∨ ((p2 ∨ p3) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246212683795328744847463982210 : ((p4 ∧ p3) ∨ ((p2 ∨ ((p5 ∨ (True ∨ p4)) ∧ (p5 → (p3 → ((p4 ∨ (True → p5)) ∨ True))))) ∨ (False ∨ ((p4 ∧ (p5 ∨ p2)) → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_102715825132104559287068471997 : (((((p5 ∧ ((p5 ∨ p3) ∨ p2)) ∧ (False ∨ (False ∨ ((((p2 ∧ True) ∧ p2) ∨ p5) → (p5 → (p3 ∧ p2)))))) ∨ False) ∨ True) ∧ (p2 → p2)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60038771383989979034932756475 : (((p1 ∨ p4) → ((True → ((p3 → (False ∧ (True ∧ p1))) ∨ p1)) → (((p3 ∧ ((p5 → p1) ∧ p3)) ∧ p5) ∨ ((p1 ∨ True) → True)))) ∨ False) := by
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208491442101815517231902286227 : (((False ∧ False) → ((False ∨ True) → True)) → ((((False ∨ (True ∨ (p3 → ((True ∨ p2) → p1)))) ∨ (p1 ∨ p3)) → p4) → (p4 ∨ (p4 ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((False ∨ (True ∨ (p3 → ((True ∨ p2) → p1)))) ∨ (p1 ∨ p3)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_203883768629646349935316953110 : ((p1 → ((False ∧ (p4 ∨ p4)) → p4)) ∧ ((p5 ∨ p4) → ((((p5 → (True ∧ ((False ∧ (p3 ∨ (p4 → False))) ∨ p1))) ∧ p5) ∧ p5) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Implications on the right can always be decomposed.
  intro h5
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
theorem thm_5_vars_646424511263103380806681554193 : ((((p1 → ((((p1 → ((p4 ∨ (p4 ∧ p2)) → (True ∨ ((True ∨ ((True ∨ (True → False)) ∨ p2)) ∧ p1)))) → False) ∧ p5) ∨ p3)) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112265341976511437747907841023 : (((p5 ∨ (((p3 → p4) → ((((p1 ∨ True) ∨ ((p2 → True) ∨ p3)) → (p3 → p5)) → p1)) → ((True ∧ p3) ∧ False))) ∨ p1) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4471713547014300339574419858 : (p2 → ((((p4 → (False ∨ ((p1 ∨ p5) → p1))) ∨ (p5 ∨ True)) → False) → (p1 ∨ ((((p1 ∧ False) → p5) ∧ p5) ∧ (p4 → False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((p4 → (False ∨ ((p1 ∨ p5) → p1))) ∨ (p5 ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159712911049070528661234917243 : ((((((((p1 → p2) → p4) → p5) → p5) ∨ (p2 → False)) ∧ ((p4 ∧ True) ∧ (p2 ∨ p2))) ∨ p2) → (False ∨ (((True ∨ p3) → p4) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h4.left
      let h7 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h10 =>
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
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h4.left
      let h14 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h15 := h13.left
      let h16 := h13.right
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h19 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68910039426852260843806728044 : ((p4 → (False ∨ ((p5 ∨ ((p3 → ((p5 ∨ False) ∧ ((p3 ∨ ((p5 → (True ∨ True)) → p1)) → (True ∧ p2)))) ∧ (p2 → p1))) ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51899576263119763513039449325 : ((((True → (((p2 → p4) → (p3 → ((p5 → p5) ∨ (p5 → p1)))) ∨ True)) → p3) ∨ ((((p3 ∧ (p5 → p1)) ∧ p3) ∧ False) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64827499385884780372078828360 : ((p2 ∨ ((((p3 ∨ ((p4 ∧ p4) → (p1 ∧ (p2 ∧ False)))) ∨ (p1 ∧ (p2 → True))) ∨ ((False ∧ False) ∨ (p1 → (p5 ∨ p5)))) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337044975399151668284622566726 : (p1 → ((((((p5 → (p3 ∧ p1)) → ((p1 → p5) ∧ (((p3 ∧ p3) ∧ (p1 → (p5 ∧ False))) ∧ False))) ∨ p3) ∧ p4) ∨ True) ∨ (p4 → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_974750625960861406362476460711 : ((((p2 → True) → (((((((p2 → p3) ∨ p4) ∨ (((((False ∨ p4) ∧ p5) ∨ p1) → False) ∧ (p5 → p3))) ∨ p5) ∨ p4) ∧ p2) ∧ False)) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64172831926858122480193590557 : ((False ∨ ((p5 ∨ p1) ∨ (((((p4 ∧ p2) → p1) ∧ ((True ∨ p4) → (p2 ∨ ((False ∧ True) ∨ False)))) ∧ p4) ∨ (p2 ∨ (False → p2))))) ∨ False) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303343126584057225869901895162 : (p1 ∨ (((((p1 → p3) ∧ p2) → ((((p5 ∧ True) → p3) → True) → (p2 ∧ (((False → p2) ∨ p4) → ((p5 ∧ p1) ∨ True))))) ∨ False) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h1.left
    let h8 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h1.left
    let h11 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135455106731127324362321219203 : ((((((p4 → ((False → (p1 → True)) → ((p3 → p3) ∧ (p3 ∧ p3)))) ∧ p2) ∧ True) → False) → (p3 → (p2 ∨ False))) ∨ ((False → p5) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52016437149266616928587979504 : (((p5 ∧ ((False ∧ False) ∨ ((p2 ∧ p4) ∧ ((p2 ∨ (p3 ∨ (p3 → p1))) ∧ False)))) ∨ ((p3 ∧ (False → p1)) → (p1 ∨ (p5 → p5)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347390876613632179947703076591 : (p3 → ((p1 ∨ ((p2 ∧ (p1 ∨ p3)) → (p5 ∨ p4))) ∨ (p1 ∨ ((False → (((((p4 ∨ p3) ∨ (p1 ∨ p2)) ∧ False) ∧ False) → p3)) → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133835550903789371837346095313 : ((((p2 ∨ True) → ((((p4 ∨ ((False ∧ p5) → p4)) ∧ (p3 ∨ p4)) ∨ (p5 ∧ p2)) → (p1 → (p1 → p2)))) ∧ True) ∨ ((False ∨ p2) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118249981114360996894577182476 : ((p1 ∨ ((p1 ∨ ((((((False ∧ p3) → (p2 → p3)) ∨ (p5 ∧ p1)) → p1) ∨ (False → p1)) ∨ p3)) ∧ ((p4 ∨ True) ∧ True))) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248277864395842818377087085734 : ((p2 ∨ p2) ∨ (((p4 ∧ (True ∧ p4)) ∧ (((p2 ∨ ((p1 ∨ p5) → (True ∧ p2))) → True) ∧ p1)) → ((p1 → p2) ∨ ((p1 → p2) → True)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43990262816508886807049690920 : ((((((False ∨ True) ∧ (False ∧ (False ∧ ((True ∧ (True → True)) ∧ (p5 ∨ (p1 → (p5 ∧ (p5 ∨ p2)))))))) ∨ True) → (p3 ∧ p5)) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659067410636542222865497668749 : ((((p2 → ((True → ((((p3 ∨ False) ∧ p1) ∧ p4) → (True → (False ∨ (p4 ∧ ((False → p5) → p1)))))) → (p5 → p3))) ∨ (False → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_144939811416011128809561017297 : ((((p2 ∨ (True ∧ (False ∧ ((True ∨ p4) ∨ ((p2 → p1) ∧ p1))))) ∨ p4) → (p3 ∨ ((p3 ∧ p3) ∨ True))) ∧ ((False → p3) ∨ (True ∨ p2))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
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
    -- True on the right can always be proven directly.
    apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115534695557317614123176101819 : (((True ∨ ((p5 ∨ p4) ∧ (False ∨ (p1 ∧ p5)))) → ((p2 ∨ (p5 → ((p1 ∨ (False ∧ (p4 → p5))) ∨ p3))) ∨ (p3 ∨ p3))) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616416469823950459070802394314 : (((((((p4 ∨ ((p5 ∨ (p4 ∧ (True ∨ p2))) ∧ p2)) ∨ p1) → True) → (True → (((((p1 ∨ p3) → p4) → p2) → p3) → p4))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110545423422033227327949456264 : ((p4 → (True ∧ ((p2 ∧ (((p2 ∨ (p3 → ((p2 ∧ True) ∧ p4))) ∧ p3) ∨ p2)) ∨ ((p4 ∨ p1) ∨ ((p1 ∨ p3) → p3))))) ∧ (True ∨ False)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300526211943786824974709808409 : (False ∨ ((p5 ∨ (p2 → ((True ∧ p4) ∨ ((p2 → (((p4 → p1) ∧ p1) ∧ (p2 ∧ p5))) ∨ (p4 ∨ True))))) ∧ (p1 ∨ ((p4 ∨ True) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64658744644550828387346666773 : ((p1 ∨ (False ∨ ((((((p3 ∨ p3) ∧ (p2 ∨ (False ∨ p1))) ∨ p3) ∨ p5) ∨ ((p2 ∨ (p2 → ((p2 → False) ∨ True))) ∧ True)) ∨ p1))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165935742604338580416388456691 : (((True ∨ True) ∧ ((p5 → False) ∧ ((p4 ∨ (((p1 ∨ True) ∨ p3) → p5)) ∧ (p2 → p1)))) ∨ (p1 → (True ∨ (p3 → ((p5 ∧ False) → p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116581015761113437224486506613 : (((p3 ∨ p5) ∧ (p2 ∨ (p5 → ((((p1 ∨ False) ∨ True) ∧ (False ∧ ((p2 → p5) ∨ (p4 ∧ (False ∧ (p2 ∧ p2)))))) ∧ False)))) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261444293259448008776166559413 : ((p5 → p2) → ((p2 ∧ (p1 ∨ ((p2 → (p1 ∨ p2)) ∧ (True ∧ ((((p2 ∨ p1) → ((p5 ∨ p5) ∧ p5)) ∧ p2) → (p4 → False)))))) → p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43603428345166405278802131557 : (((((((((p2 ∧ (p5 ∧ (False → (p1 ∨ p2)))) ∨ (p4 → p2)) → p3) → ((p1 ∨ False) ∨ (p3 ∨ True))) ∨ p1) → p1) → p4) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_692170323985542975797482260527 : ((((((((p4 → p1) → ((p1 ∨ (p4 ∧ p2)) ∨ False)) → p5) → p3) ∨ p4) ∧ ((p1 ∧ p2) → (p3 → ((p2 ∧ False) ∨ (p4 ∨ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113421631808643150703104236825 : (((((p4 ∧ p5) ∨ (False ∧ (p1 → ((p3 → True) ∧ ((p3 ∧ (p4 ∧ p4)) ∨ (p3 ∨ (p3 → p3))))))) ∧ p3) ∨ (True → True)) ∨ (p4 → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177936050516851335070521852074 : (((((True → p5) → (True ∨ p5)) → (((p5 → p3) ∨ p1) ∧ True)) ∨ p1) ∨ (True ∨ (False → ((((p4 → (p3 → p1)) ∨ True) ∨ False) ∧ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_90335283481360570208831848555 : (((p3 → (p5 ∨ True)) → (((((p4 ∧ (p1 ∧ p5)) ∧ (p2 → (p4 ∨ (((True ∧ p4) ∨ (True ∧ p3)) → p3)))) ∧ p3) ∨ True) ∧ p2)) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 → (p5 ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_25483313945968392132584085050 : (((p5 ∧ (p3 → p3)) → ((((p4 ∧ (True → (p2 ∧ False))) ∧ p4) ∨ ((p5 → (((p3 ∧ p1) → p1) ∧ p2)) → p1)) ∨ (False → False))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671652574450538628946701032435 : ((((((((((p5 ∨ (p5 → p1)) ∨ p3) → (((p2 → p3) ∨ False) ∨ p1)) → p5) ∧ (p4 ∧ True)) ∨ p1) ∧ p1) → ((True ∨ p2) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52500062323852784135818657343 : (((((((True ∨ (False → (True → p1))) ∧ p3) ∧ (p4 ∧ p4)) ∧ p3) ∧ False) ∨ ((True ∨ ((False ∨ p1) ∧ p1)) ∨ (p3 ∨ (p4 ∧ p5)))) ∨ p1) := by
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
theorem thm_5_vars_746741698060566369412703156376 : ((((p3 ∨ p3) → ((((p3 → True) ∧ p5) → ((p1 → (p4 ∨ (((True ∧ True) → p4) ∧ False))) ∧ p4)) ∧ ((False ∧ (p1 ∧ False)) ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_163221952068756915786539547922 : (((((p1 → p5) → p3) ∨ (False ∨ (p5 ∧ p4))) ∨ (((p2 ∨ p3) ∧ (p5 ∧ p3)) → p3)) ∧ (((p2 ∧ (p2 ∨ (True → p3))) ∨ p2) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    let h5 := h3.left
    let h6 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h3.left
    let h9 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h9
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55470933165077761639706504015 : ((((False ∨ (p2 ∨ p5)) ∧ (p5 ∧ p4)) → ((p5 → (p4 → p2)) ∧ ((p1 ∧ ((((True ∨ False) ∨ (p1 → p2)) ∨ p2) ∨ False)) ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156595252066482472638550577037 : ((((((p5 ∧ (p1 ∨ (p2 ∧ p2))) ∨ (p2 ∨ (p3 ∧ ((p5 ∧ p1) → p1)))) ∨ True) ∧ p2) ∧ p2) ∨ ((p1 → (p4 ∨ (True → p5))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323202111042221733996654451194 : (p5 ∨ (((((p4 → p3) ∧ ((p4 → ((p5 ∨ (False ∧ (p2 ∨ p3))) ∧ p2)) → False)) → (p1 ∨ (p2 → p4))) ∨ (False → p5)) ∨ (p4 ∧ p2))) := by
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
theorem thm_5_vars_184611113872074564843684602778 : (((((p3 → (p5 ∨ p4)) → p4) → p5) ∧ ((True ∨ p2) ∨ p1)) ∨ (p5 → ((((((True ∨ False) → p1) ∨ p5) → False) ∨ p5) → (False ∨ p5)))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161729642209722030905182553187 : ((p3 ∨ (((p5 ∨ ((p5 → p1) ∨ True)) → (True → False)) ∧ (False ∨ (((p4 ∧ p4) ∨ False) ∨ False)))) → (((True ∧ (p2 ∧ p3)) ∨ p3) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Conjunctions on the left can always be decomposed.
          let h10 := h9.left
          let h11 := h9.right
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h12 : (p5 ∨ ((p5 → p1) ∨ True)) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h13 := h4 h12
          -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
          have h14 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h13, we can now drive its conclusion.
          let h15 := h13 h14
          -- False on the left can always be used.
          apply False.elim h15
        case inr h16 =>
          -- False on the left can always be used.
          apply False.elim h16
      case inr h17 =>
        -- False on the left can always be used.
        apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324527689693125356378084042873 : (p5 ∨ ((((p1 → p2) ∨ p2) ∨ p5) → (p1 → ((p4 ∨ (p2 ∧ ((((p1 → (p5 ∨ (p5 ∨ False))) ∨ True) → False) ∧ p5))) → (False ∨ p1))))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
    case inr h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200364245042801049753983920487 : (((p1 → p5) ∧ (((p4 ∨ p5) ∧ p4) ∨ p2)) → (p4 → (((p5 → (True → (p1 → p3))) ∧ p2) ∨ (((True ∨ p5) ∨ (p4 ∧ p1)) ∨ True)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49046483425463145075675569306 : ((((p5 → ((True → p1) ∧ ((((p3 ∧ p3) ∧ p5) ∧ (((True → p3) → p2) ∧ False)) → (p5 ∧ p1)))) → p4) ∨ (p1 → (True → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134551611510837847081936200530 : (((((p4 → False) ∧ (p1 → ((p4 ∧ (False ∨ (p5 → p5))) → (p3 → (p1 ∨ (False ∨ (False ∧ p3))))))) → p1) → p5) ∨ (False ∨ (True ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69161265191918140878746330851 : ((p5 → (((p5 ∨ (((True ∨ (p5 → ((p1 ∨ p2) → p4))) ∨ p1) ∧ ((False ∨ p3) ∧ True))) ∧ True) → (p3 → ((p5 ∨ p2) ∧ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53102450317973053822530550138 : (((p5 ∨ (p3 ∧ ((p5 → p3) ∧ (((True ∧ False) ∨ p5) → p4)))) ∧ (False ∨ (False ∨ (((p2 → True) ∧ (True ∧ (p3 → True))) ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668428701903315251432023222446 : ((((((p2 ∨ (p4 ∨ (((p3 → p5) ∧ p5) ∨ (((True → p4) → (False ∧ (p1 → p2))) → p1)))) ∨ p2) ∧ True) ∨ ((p2 ∧ p5) → True)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_37435211644119715756671111218 : (((((p4 ∧ (((p3 ∧ ((p2 ∧ ((p1 ∨ p2) → p3)) ∨ p2)) ∧ True) ∨ (p4 ∧ p4))) ∧ (p1 ∨ (p1 → (p3 ∧ p4)))) ∨ p3) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



