variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114892060995685129919203073357 : (((False ∨ (p5 ∨ (((p2 ∨ p1) ∨ (((p1 ∨ False) → p3) → p5)) ∧ p3))) ∨ (True ∨ ((False → True) → ((p5 ∨ p3) → p4)))) ∨ (True ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135669004598664336834129106371 : (((p1 ∨ ((False ∧ (p3 ∨ p3)) ∨ (((p5 ∧ (False ∧ False)) ∧ (p2 → p3)) → p5))) → ((p2 ∨ p2) ∧ (p5 ∧ p4))) ∨ (p5 → (p2 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213646100154712300246920590245 : ((((p2 ∨ p2) ∨ False) ∨ p1) ∨ (p3 ∨ (p4 ∨ ((p3 → (True → (p3 ∨ (False ∨ p5)))) ∨ ((p2 ∧ p3) → ((False → p2) ∨ (p4 → p4))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231799784561535090487620596234 : (((p4 ∧ p2) → p2) → (((((p1 ∧ ((True ∧ False) → ((p2 ∨ True) → p5))) ∧ ((p2 ∧ p4) ∧ p5)) ∨ p3) ∧ (True → p2)) ∨ (p2 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780402712039756250531640069376 : (((p2 ∨ (((p4 → ((True ∧ False) → p3)) → (p1 ∨ (((True ∨ True) ∧ (p1 → p5)) ∨ p2))) ∨ ((p1 ∨ (True ∨ (True → True))) ∨ p1))) ∨ p4) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2291774519361879120026373735 : ((p2 ∧ (False ∧ ((p1 ∧ False) ∧ ((True ∨ (True → p3)) → (p2 ∧ p5))))) ∨ (p5 ∨ (True → ((False → (p3 ∧ p4)) ∨ (p3 ∧ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263889517468980770994676623359 : (True ∧ (((((p2 ∧ ((False ∧ p1) ∧ p3)) ∧ p5) ∨ (True ∨ p1)) ∨ (p2 ∨ p2)) ∨ (((p1 → True) → (p4 ∨ (False ∧ True))) ∧ (True → p1)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_606002083533883569801982237118 : ((((p5 → (((False ∨ p2) ∧ (p3 ∧ p2)) → ((p4 → p2) → ((p2 ∧ (p5 → (p4 ∧ p2))) ∨ (p1 ∧ ((p2 ∧ p4) ∧ p4)))))) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149285362728582963502998066669 : (((p3 → False) ∨ ((((((False ∧ True) → (False ∨ (p2 ∨ p5))) ∧ p1) ∧ (p3 ∨ p4)) ∧ (p1 ∧ p5)) ∨ True)) ∨ (p4 → (p2 ∨ (p2 ∨ False)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259096079157112485603449845858 : ((True → p5) → ((p5 → (p3 ∧ (p5 → p3))) ∨ ((((True → False) ∧ (p3 → True)) ∧ p2) → ((((p1 ∧ p3) → (True ∨ False)) ∨ False) → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138341182732618314434696058887 : ((p4 → ((((p4 → p2) → p4) → ((p5 → p1) ∨ ((p5 ∧ p3) ∧ (True ∨ ((p1 ∨ (p2 ∧ p4)) ∧ False))))) ∧ False)) ∨ (p3 → (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658843694024428338029816539047 : ((((True → ((p1 ∧ (p5 ∨ ((((p2 → p3) ∧ True) → p1) ∨ (p5 ∨ p3)))) ∨ (((p3 ∨ p5) → p4) ∨ (p1 → True)))) ∨ (True ∧ p2)) ∨ p4) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214713344453189559720714798487 : (((p1 ∧ p1) ∨ (p4 ∧ True)) ∨ ((p1 ∧ p2) ∨ ((False → ((p4 ∨ (p5 ∧ p1)) → p5)) ∨ ((p3 ∧ ((True ∧ p3) ∨ p1)) → (p4 ∨ p2))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h1
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355530545514984329995356697579 : (p5 → (((((((True ∨ ((True → p4) ∧ True)) ∨ p2) → (False → p5)) ∨ (p4 ∨ p1)) ∧ ((p4 ∧ (p1 → p4)) → False)) ∧ False) ∨ (p4 ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_753759211161008687256888619836 : (((False ∧ (((p1 ∨ p5) → (p3 ∧ ((p4 → ((p2 → False) ∧ p5)) → p2))) ∨ ((((p2 → False) ∨ (p3 ∧ p3)) ∨ (p5 → p5)) ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251175365152011745536132258791 : ((p2 → p1) ∨ ((p3 ∧ (((((((True → False) ∨ (((p2 → p2) ∧ True) ∧ p3)) → (p1 ∨ p3)) → p1) ∧ (p3 ∨ p3)) ∧ p3) ∧ p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46673785588043433426657348407 : (((p1 ∨ (((True ∧ (False ∨ p2)) ∧ p3) ∨ ((((p5 → (p5 ∧ p5)) ∧ True) ∧ (p3 ∧ p1)) ∨ (p3 ∨ (p4 → True))))) ∧ (False → True)) ∨ p3) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344718027810380828845047984491 : (p2 → (p3 → ((((False ∧ p3) → (((p2 ∨ (p4 ∨ ((p5 ∧ p1) ∨ True))) → p5) → False)) ∧ ((p4 → p2) → (p1 ∧ (p3 → False)))) → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : (p4 → p2) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h8 := h5 h6
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h10 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h11 := h9 h10
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55332881217898889868520780963 : (((p4 ∨ (p2 → (p4 → (p5 ∨ p1)))) ∨ ((p3 ∨ (((p3 ∨ ((p1 ∨ (p5 ∧ p2)) → False)) → p5) ∨ p1)) ∨ (p5 ∨ (p4 ∨ True)))) ∨ p5) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208845063172925812727881043159 : ((p3 ∧ (p2 → ((p3 ∨ p4) ∨ True))) → (p2 → (p3 ∧ (((p2 ∧ (False ∨ p4)) → p2) → (((p3 → p2) → ((p1 ∨ p4) ∨ p1)) ∨ True))))) := by
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
  exact h3
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41512110888397918865930527834 : (((((((p2 ∨ ((p1 ∨ p3) ∧ p5)) → False) ∨ p1) ∨ p3) ∧ ((p4 ∨ (p1 ∨ True)) ∨ ((p3 ∨ ((True ∧ p1) → p4)) ∧ p2))) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110839666873705374539405581365 : ((((p2 ∨ (True → (((((p3 → ((True ∨ p3) ∧ p2)) ∨ p3) ∨ (p1 ∧ ((p1 ∧ True) → True))) → p4) → p2))) ∨ True) ∧ True) ∨ (p1 ∧ p2)) := by
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
theorem thm_5_vars_690992106786892795492705308197 : ((((((p5 → p2) → (((p3 ∧ p1) → p4) ∨ (p2 ∨ (False → False)))) → (True ∨ p2)) → ((True ∧ p4) ∧ ((p2 ∨ (p1 ∧ False)) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48010471277996024547302480298 : (((((p5 ∧ ((((p1 → p3) ∨ p3) ∧ (p1 ∨ p2)) ∨ False)) ∧ p1) ∧ ((p4 ∨ ((p2 ∨ p4) ∧ p1)) → (False ∧ p5))) → (p1 ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50195255330409595418377906563 : ((((p2 ∨ ((p1 ∨ (((((((True → p2) → p4) ∧ False) ∨ p4) ∨ p3) ∧ p2) → p4)) → False)) ∧ p2) ∨ ((p5 ∨ (p1 ∨ p3)) → True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_730226841119312257670088187097 : (((((p1 → p1) → p5) → (((p5 ∨ ((p3 ∧ (p5 → ((p1 → False) → True))) ∧ p1)) ∧ (p5 → p3)) ∨ ((False ∨ p3) → (p2 ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136187710994146705566307226417 : ((((False ∨ (False ∧ p3)) ∨ (p5 → True)) ∧ (((True ∨ (((True → p5) → p5) ∨ p1)) ∨ ((p3 → p1) → p3)) ∧ False)) ∨ (p1 ∨ (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117109674395596582371304959577 : (((p2 → p5) → ((p5 ∨ (True ∨ p3)) → (((p1 ∧ ((False ∨ (False ∧ (p2 → (p5 ∧ (p4 ∧ True))))) ∨ p2)) → False) ∧ True))) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65956669610949146474605616938 : ((p4 ∨ (p4 ∨ (((True ∧ p3) → ((False ∨ (((True ∨ False) ∨ (p2 ∨ p5)) → (p2 → ((p5 → p3) ∧ (False ∨ p2))))) ∨ p5)) ∨ False))) ∨ p5) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h6
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h9
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h12 =>
      -- One of the premise coincides with the conclusion.
      exact h3
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h15 =>
      -- False on the left can always be used.
      apply False.elim h15
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h17
    case inr h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41064663734666952073106954590 : ((((p5 ∧ (((False → (p5 ∧ (p5 ∨ (p5 → p3)))) ∧ p3) ∨ (((p2 ∨ (p1 → True)) ∧ p5) → (False ∧ True)))) → (p4 ∧ p2)) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112907883268163160338712071527 : ((((True ∨ True) ∨ ((True → (False → ((((p5 ∨ ((False ∧ p2) → False)) ∨ p2) ∧ p3) ∨ (p5 ∧ (p1 → True))))) ∨ p4)) → p4) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342302029069274996004228853402 : (p2 → ((p4 ∨ ((p1 ∨ False) → (((False → p4) → ((p1 → (p4 ∨ p3)) ∨ (p1 ∧ p5))) ∨ True))) ∨ (p1 → (p2 → ((p2 ∧ False) ∧ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118361824955533918565531018460 : ((p2 ∨ (((p2 → (p3 ∨ ((p4 ∨ (p2 ∧ False)) ∨ (p4 → False)))) ∨ (p5 → ((p4 ∧ True) → (False → p4)))) ∨ (False ∧ p4))) ∨ (p4 ∨ p4)) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49514994871965680799056428966 : ((((((True ∨ p3) ∨ (p3 ∨ (p4 ∨ ((False → p1) ∨ p1)))) ∧ (p4 → (True ∨ (p1 ∧ p4)))) ∧ (True → False)) → ((p1 → p3) ∧ p3)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h9 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h10 := h4 h9
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- One of the premise coincides with the conclusion.
      exact h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h16 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h17 := h4 h16
        -- False on the left can always be used.
        apply False.elim h17
      case inr h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h20 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h21 := h4 h20
          -- False on the left can always be used.
          apply False.elim h21
        case inr h22 =>
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h23 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h24 := h4 h23
          -- False on the left can always be used.
          apply False.elim h24
  -- Conjunctions on the left can always be decomposed.
  let h25 := h1.left
  let h26 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h27 := h25.left
  let h28 := h25.right
  -- Disjunctions on the left can always be decomposed.
  cases h27
  case inl h29 =>
    -- Disjunctions on the left can always be decomposed.
    cases h29
    case inl h30 =>
      -- We want to use the implication h26 based on <expert-advice>. So we show its premise.
      have h31 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h26, we can now drive its conclusion.
      let h32 := h26 h31
      -- False on the left can always be used.
      apply False.elim h32
    case inr h33 =>
      -- One of the premise coincides with the conclusion.
      exact h33
  case inr h34 =>
    -- Disjunctions on the left can always be decomposed.
    cases h34
    case inl h35 =>
      -- One of the premise coincides with the conclusion.
      exact h35
    case inr h36 =>
      -- Disjunctions on the left can always be decomposed.
      cases h36
      case inl h37 =>
        -- We want to use the implication h26 based on <expert-advice>. So we show its premise.
        have h38 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h26, we can now drive its conclusion.
        let h39 := h26 h38
        -- False on the left can always be used.
        apply False.elim h39
      case inr h40 =>
        -- Disjunctions on the left can always be decomposed.
        cases h40
        case inl h41 =>
          -- We want to use the implication h26 based on <expert-advice>. So we show its premise.
          have h42 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h26, we can now drive its conclusion.
          let h43 := h26 h42
          -- False on the left can always be used.
          apply False.elim h43
        case inr h44 =>
          -- We want to use the implication h26 based on <expert-advice>. So we show its premise.
          have h45 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h26, we can now drive its conclusion.
          let h46 := h26 h45
          -- False on the left can always be used.
          apply False.elim h46



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207211601369488993946157442282 : ((((p5 ∨ (p2 ∨ p1)) ∧ p4) ∨ True) → ((p5 ∧ ((((p2 → p3) ∨ (p3 ∧ False)) ∧ ((p1 ∨ p5) ∧ p5)) → p2)) ∨ ((p4 ∨ p5) → True))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h9
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h13
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165380452021893782355151894618 : (((((True → p3) → ((p4 ∧ p1) ∧ p4)) ∨ ((p5 ∧ p3) ∨ p2)) ∨ ((True ∨ p4) ∨ p2)) ∨ (p2 ∧ (p3 → (p5 → (False ∧ (True ∨ p4)))))) := by
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
theorem thm_5_vars_524552183981418982177769263864 : (((True ∧ (((p1 ∧ (p1 → p1)) ∧ True) → ((((((p5 ∧ True) → (False ∨ False)) ∨ p5) ∧ ((True ∧ p3) ∧ (p1 → p5))) ∧ p4) ∨ True))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_706792408493798828919035489801 : ((((((False ∨ False) ∧ ((p3 ∨ False) ∨ p3)) ∧ p3) ∨ ((((p1 → (p5 ∨ (p1 ∨ False))) → (p2 ∧ (p4 ∨ (p2 → p3)))) → True) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_127781448331805209028082306614 : ((True → ((((((True ∨ p5) ∨ p5) ∧ (p4 ∧ False)) ∨ p5) ∧ p4) ∧ ((True ∧ (False ∧ (p5 → True))) ∧ (p3 ∨ (False ∨ p2))))) → (p3 ∨ p1)) := by
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
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313223318490613302021090259601 : (p3 ∨ (((True → (p5 → True)) → (p4 → ((True ∧ True) ∧ (False ∧ (((((True → p2) ∧ p5) ∨ (p3 ∧ (p2 ∨ p2))) ∧ p2) ∧ True))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_937387998808867605305936957719 : (((((True → p4) ∧ ((p5 ∧ p3) ∨ p2)) ∧ (((((False ∨ ((p1 → ((p4 ∨ (p3 ∧ False)) → p5)) ∨ p3)) ∧ p3) ∧ False) ∨ True) → p1)) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    let h7 := h6.left
    let h8 := h6.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h10 := h4 h9
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h12 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h13 := h4 h12
    -- One of the premise coincides with the conclusion.
    exact h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152850286464499402022063236744 : (((p3 → True) → (p2 ∧ (True ∧ ((((p3 → (p3 ∧ p4)) ∧ ((p2 → True) ∧ (False ∨ True))) ∨ p1) ∧ False)))) → ((True ∧ p2) → (p1 → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : (p3 → True) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h6
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249563260351672068125178208235 : ((p5 ∨ p2) ∨ (((False ∨ p5) ∨ p3) ∨ ((True ∨ ((p5 ∧ p3) ∨ (p2 ∨ (p5 → (((True ∨ p1) → True) ∨ ((p5 → True) ∧ p4)))))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_803289535019226398285134234396 : (((p3 → ((((p1 → True) ∨ (((p5 → (p3 ∧ (p2 ∧ True))) → (p5 ∨ p4)) ∧ p2)) → (False ∧ (p1 → ((p1 → True) ∧ p2)))) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_120995570313558179693739227841 : ((((False → p2) ∧ ((p2 → False) ∨ ((p1 → True) ∨ ((True ∧ ((p5 ∨ (p5 → (p4 → (p3 ∧ True)))) → p4)) ∨ p2)))) ∨ True) → (p2 → p2)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Conjunctions on the left can always be decomposed.
          let h11 := h10.left
          let h12 := h10.right
          -- One of the premise coincides with the conclusion.
          exact h2
        case inr h13 =>
          -- One of the premise coincides with the conclusion.
          exact h13
  case inr h14 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809763173024588254481682272705 : (((p5 → (((p4 ∨ ((p2 ∧ (((p4 → (p4 ∧ True)) ∧ p4) → (False ∨ (True ∨ (p4 → (False ∧ False)))))) ∨ p1)) → False) ∨ (p5 ∨ p3))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265572419946309491744487793835 : (True ∧ (p1 ∨ ((((p4 ∧ p5) ∨ ((p2 → p3) → ((((((p3 → p5) → True) ∧ (False ∨ (True ∨ p5))) ∨ p3) ∧ p5) ∧ p1))) ∨ True) ∨ p2))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_149388334565262322554995879222 : (((p5 → p1) → ((((p5 → ((((p3 ∧ p3) ∨ p5) ∨ p5) ∨ (True ∧ p3))) ∧ (p1 → p1)) → p4) ∨ p3)) ∨ (((False ∧ False) ∧ p1) → p5)) := by
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
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259641285362439480473660250497 : ((p1 → False) → ((p2 ∨ ((p5 ∨ (False ∨ True)) ∨ p3)) → (p1 ∨ ((p1 → (True → p3)) ∨ (((p1 ∧ p4) → (p5 ∧ (False ∨ p4))) → p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h8
        -- Implications on the right can always be decomposed.
        intro h9
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h10 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h8
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h11 := h1 h10
        -- False on the left can always be used.
        apply False.elim h11
      case inr h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- False on the left can always be used.
          apply False.elim h13
        case inr h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h15
          -- Implications on the right can always be decomposed.
          intro h16
          -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
          have h17 : p1 := by
            -- One of the premise coincides with the conclusion.
            exact h15
          -- We have shown the premise of h1, we can now drive its conclusion.
          let h18 := h1 h17
          -- False on the left can always be used.
          apply False.elim h18
    case inr h19 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h20
      -- Implications on the right can always be decomposed.
      intro h21
      -- One of the premise coincides with the conclusion.
      exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_109197013429224091751466796962 : ((False ∨ (((((p2 ∨ p1) ∧ ((p1 ∨ p3) ∨ ((p1 → ((False ∧ p1) → p3)) ∨ p5))) ∨ (p5 ∧ p4)) ∧ p5) ∨ (False → p3))) ∧ (False ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322205681702770487032866465661 : (p5 ∨ (((((((False → p3) → p4) ∧ (True ∨ p2)) ∨ ((((p4 → False) ∨ (p5 ∨ (p5 ∧ True))) ∨ True) → (p2 ∧ p4))) → False) ∧ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152790717150084717899491776760 : (((p3 ∧ p4) → (((False ∨ ((p4 → p5) ∧ (True → p3))) ∨ (False → (True → ((p4 → p2) → p1)))) ∧ p3)) → (((p1 ∧ False) ∨ True) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347290149008799712339669144309 : (p3 → (((p4 → p2) ∧ (p1 ∨ ((p1 ∧ (p5 ∧ False)) ∨ p1))) ∨ (p5 ∨ (((((p1 ∧ (p4 → (p5 → p5))) ∨ p2) ∧ p3) ∨ p2) → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151874479280573551528467120204 : (((p3 → ((p3 → ((False → p3) → p2)) → (p1 ∧ (p1 ∨ (True → p3))))) ∨ ((p5 → p2) → (p2 ∧ p4))) → (((p2 → p3) ∧ p4) ∨ True)) := by
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
theorem thm_5_vars_319029780818572442705307975906 : (p4 ∨ (((((p3 ∧ (p3 ∨ p5)) ∨ p3) ∨ ((True → ((p2 → ((p4 ∧ True) → p4)) ∨ p3)) ∨ p4)) ∨ p2) ∨ (((p4 ∨ p4) ∨ False) ∨ p4))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255202172491777963528923967307 : ((p4 ∧ p4) → ((p5 → ((p3 ∧ ((((p4 ∨ p1) → p1) → p3) ∨ p3)) ∧ (True ∨ p2))) ∨ (True ∧ (p2 ∨ (((False → True) → p1) ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309779225981396338730986130011 : (p2 ∨ ((((((True ∨ False) ∨ p1) ∧ p2) ∨ (p3 → (p5 ∧ ((True ∧ ((True → p1) → p4)) → False)))) ∧ p1) ∨ (False → (True → (False → p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67700493935622456408003507738 : ((p1 → (p4 → (p3 ∨ (((p2 → p3) ∧ True) ∨ ((p5 ∧ ((p1 ∧ (((p1 ∧ True) → p3) ∨ (p3 → (True ∨ p4)))) ∨ p4)) → p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_873347517869959483896134773722 : ((((p2 → (((p3 ∧ p4) ∨ (p3 ∨ ((p2 → False) → p3))) ∨ (((True ∨ p1) → p2) ∨ (((False ∧ p4) → p1) → (p2 ∨ False))))) → p2) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 → (((p3 ∧ p4) ∨ (p3 ∨ ((p2 → False) → p3))) ∨ (((True ∨ p1) → p2) ∨ (((False ∧ p4) → p1) → (p2 ∨ False))))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_672836598675247538786269929865 : (((((p4 ∨ ((True ∧ (((p3 → p5) ∨ ((p1 ∨ p1) ∨ False)) ∨ p3)) ∧ (p1 ∨ p1))) ∧ ((True ∧ p5) ∨ p1)) → ((p4 ∨ p4) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256763797297511831893197649917 : ((p1 ∨ p2) → ((((((True ∨ p4) ∨ ((p1 → True) ∧ True)) → ((p2 ∧ p4) ∧ ((((p4 → True) ∨ p3) → False) ∧ p4))) ∧ p5) ∧ p1) → p3)) := by
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
    have h8 : ((True ∨ p4) ∨ ((p1 → True) ∧ True)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h9 := h5 h8
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- We need to get the left conjuct of h10 based on <expert-advice>.
    let h11 := h10.left
    -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
    have h12 : ((p4 → True) ∨ p3) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h13
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h11, we can now drive its conclusion.
    let h14 := h11 h12
    -- False on the left can always be used.
    apply False.elim h14
  case inr h15 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h16 : ((True ∨ p4) ∨ ((p1 → True) ∧ True)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h17 := h5 h16
    -- We need to get the right conjuct of h17 based on <expert-advice>.
    let h18 := h17.right
    -- We need to get the left conjuct of h18 based on <expert-advice>.
    let h19 := h18.left
    -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
    have h20 : ((p4 → True) ∨ p3) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h21
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h19, we can now drive its conclusion.
    let h22 := h19 h20
    -- False on the left can always be used.
    apply False.elim h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321018960139439328241751554063 : (p4 ∨ (False ∨ ((p5 ∨ (False → p2)) ∧ ((p3 ∧ True) → (True ∧ ((p2 ∨ p2) → (p4 ∨ (((p4 ∧ p2) ∨ (p5 ∧ p5)) ∨ (True ∨ p1))))))))) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h2.left
    let h6 := h2.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h2.left
    let h9 := h2.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136235674708767110615499746763 : ((((p5 ∧ p1) ∧ ((p2 ∨ p2) ∨ False)) ∨ ((True ∧ p5) → (True ∧ ((((False ∨ p3) ∨ (False ∧ p1)) ∨ p5) ∧ p4)))) ∨ ((p4 → False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125535064469244013446048374948 : (((True → p1) ∧ (p3 ∨ (p4 ∨ (((p3 ∧ True) ∨ (p4 ∧ p5)) → (((p5 ∧ p4) ∧ (False ∧ True)) → (p3 ∧ (False ∨ p1))))))) → (p1 ∨ p3)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h7 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h8 := h2 h7
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h10 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h11 := h2 h10
      -- One of the premise coincides with the conclusion.
      exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_628769289963124432652496084559 : (((((p1 → (False → (((((((((p2 ∨ (True ∧ p4)) ∨ p5) → (p3 ∧ p4)) ∧ p4) ∨ p4) → True) ∧ True) ∨ True) ∧ True))) ∧ p1) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151761127221878836647401380411 : ((((p4 ∨ (((p4 ∨ False) → p5) → (p1 ∧ ((False → p5) ∨ p2)))) ∨ (p1 ∧ p3)) → ((p4 ∧ p2) ∨ p5)) → ((p1 ∨ False) ∨ (False → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309919102439187243351750388345 : (p2 ∨ ((((False ∧ p1) ∨ ((p1 ∨ (p1 ∨ (p3 ∨ ((True ∨ p1) ∧ p4)))) → False)) ∧ (p2 ∨ p2)) ∨ (p3 → ((p3 ∨ (True ∨ p3)) ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_799794143563245683963209290429 : (((p1 → (p3 → (((p4 ∨ ((p2 → (p4 ∨ ((p3 ∨ (((p5 ∧ False) ∨ False) ∧ (p2 ∨ (p1 ∧ True)))) ∧ p4))) → p5)) → p2) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_691166076128780374703247053562 : ((((((False ∨ (True ∧ (p3 ∧ p1))) ∨ p4) ∧ (p1 ∨ (((p3 → p4) ∧ p1) ∧ p2))) → (((p2 ∧ (p2 ∧ p5)) ∨ (p4 ∨ p3)) ∨ p2)) ∨ False) ∧ True) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h11 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- Conjunctions on the left can always be decomposed.
        let h15 := h13.left
        let h16 := h13.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h14
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h18 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h17
    case inr h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h19.left
      let h21 := h19.right
      -- Conjunctions on the left can always be decomposed.
      let h22 := h20.left
      let h23 := h20.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h21
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261218605373472022478613087647 : ((p4 → p5) → (((p5 ∧ True) ∧ (p4 ∨ ((p2 → True) ∨ p5))) → ((((p1 → True) → False) ∨ p3) ∨ ((p4 → (True ∨ p3)) ∨ (p2 → p4))))) := by
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
  cases h4
  case inl h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h11
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h13
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174653903829786152918474598958 : ((((p4 → p3) ∨ p1) ∧ (((False → True) → (False ∧ p5)) → (p5 ∨ (False ∨ False)))) → ((p3 ∧ (p4 ∨ (p3 → False))) ∨ (p2 ∨ (True ∨ p1)))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_663422888433266589752025601812 : (((((False ∨ p2) → (((((p4 ∨ ((False ∧ False) ∨ p4)) ∨ (p2 → p1)) ∧ (p3 ∧ p2)) ∧ (p4 ∨ (p4 → True))) ∧ p3)) → (p3 → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345592609342966755746002973475 : (p3 → (((p5 ∨ p2) ∧ ((((p5 → ((p4 → p5) ∨ (((p5 ∧ p2) ∨ (p5 ∧ (p1 ∨ p2))) → p3))) ∧ False) → (True ∨ p5)) → p2)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354812534047007115436043459366 : (p5 → (((p1 → ((p1 ∨ p3) ∧ p4)) → (((p4 ∧ (p2 ∧ ((p3 ∧ p5) ∧ p1))) ∨ ((p5 → p2) ∨ (p4 → (p5 → p5)))) ∧ p1)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175365599632988335051904061086 : ((p5 ∨ (p3 → ((p5 ∨ ((p2 ∧ p1) ∨ (False ∧ ((True ∧ p2) ∨ True)))) ∨ p2))) → ((p2 ∨ ((p2 ∨ (False → True)) → (p4 ∨ False))) ∨ True)) := by
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
theorem thm_5_vars_613961615058376724665841096565 : (((((((((True ∧ (p5 → p1)) ∧ (p4 → (p3 ∧ False))) → p1) ∧ p3) → (False ∧ (p3 ∨ (p4 → p1)))) ∨ ((p4 ∧ p4) → p4)) ∨ False) ∨ False) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41015515779073271307255502243 : (((((p3 ∧ (p5 ∨ ((p2 ∨ (False → (False ∧ (p4 ∨ (False → ((p2 ∨ (False ∨ p2)) → p3)))))) ∨ p5))) ∨ p2) → (False ∨ p3)) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65938160213307587790079335351 : ((p4 ∨ (False ∨ (p2 ∨ (p3 → ((p2 ∨ (((False → (p1 ∨ p1)) ∨ p1) ∧ (p2 ∨ (p5 ∨ (p2 ∨ (p3 ∨ p1)))))) ∨ (True → p2)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699525144546665568154656843357 : (((((p4 ∧ ((True ∨ (p1 → ((False ∧ False) ∨ p2))) ∨ False)) ∨ p3) → ((p1 ∨ False) ∨ (((p1 → (p3 ∧ p4)) ∨ (p3 → True)) ∨ p2))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h7
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h9
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_14952372806928951179178458954 : ((((p1 ∨ (p5 ∨ p5)) ∨ (((p4 ∨ ((((True ∧ p5) ∧ p3) ∧ p4) ∨ p3)) → (p4 ∧ (p2 ∨ p1))) ∧ (p5 ∨ p3))) ∨ (p5 ∨ True)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53849324165916483364305391771 : (((((p4 ∨ p3) ∧ p3) ∧ (p2 → (p5 ∧ (p2 ∧ p2)))) ∨ (((((True → (p1 → False)) → p3) ∨ p2) ∨ ((p2 → p1) ∧ p4)) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118846169363013476035663316460 : ((True → ((((p4 ∨ (p2 ∧ (False → p1))) ∨ False) ∧ (((p1 ∨ (p1 ∨ p1)) ∨ False) ∧ p5)) ∨ (p3 → ((p3 ∨ p2) ∧ True)))) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219078662490282410686436492748 : ((p5 ∧ (p1 → (p1 → p4))) → ((p5 ∧ True) ∧ (p5 → (p1 ∨ ((p3 ∧ (p4 → (True ∧ ((True ∧ p1) ∨ p1)))) ∨ (False → (True → p2))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41304999505902839776732623156 : ((((((p3 → ((True ∨ (True ∨ (False ∨ False))) → p5)) ∧ (p5 ∨ (p5 → p4))) ∧ False) ∧ ((p2 ∧ (p3 ∧ p5)) ∧ (True ∧ False))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40412178347296207310705517338 : ((((((p4 ∨ ((p3 → (p5 ∧ (p1 → (p4 ∨ ((p3 → False) → p2))))) → p5)) ∨ False) ∨ (((p4 ∨ True) ∨ p3) → True)) ∨ p4) ∨ False) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_34987503493294637448675942339 : ((p1 → (((p1 ∨ False) → ((p3 ∨ p5) ∧ (((True ∧ (p4 ∧ (p1 → (True ∧ (((p3 ∧ p1) ∨ p4) ∨ p5))))) ∧ p5) ∧ p2))) ∨ True)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249493950280657351446246901789 : ((p5 ∨ p1) ∨ ((True ∨ ((((p2 ∧ True) → (((p5 → p5) → p3) ∨ p1)) ∨ p2) ∧ True)) → (p1 ∨ (True ∨ (True ∨ (True → (p2 ∧ p5))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
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
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114521077390447186781220263109 : (((p3 ∧ (((p1 → p1) ∨ (((p4 ∨ (p1 ∧ p4)) → ((p5 → p3) → True)) ∨ p3)) ∨ p3)) → ((p5 ∨ True) → (p5 ∨ False))) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46617809711815097229312292531 : (((p3 ∧ ((p3 ∧ ((False ∧ (p3 ∨ (True ∧ p1))) → (p3 → p1))) ∨ (((True ∨ (False → (p3 ∨ p4))) → False) ∨ p2))) ∧ (p2 ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2958262903933329612831923180 : ((False ∧ (p3 ∨ p3)) ∨ ((((((p5 → ((p1 → p3) → p1)) ∧ p5) → p3) → p5) ∧ (((p4 ∨ p3) ∨ (p2 → p1)) → True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_202562744913028479558011548307 : (((p1 ∨ (p5 → True)) ∨ (p3 ∧ p1)) ∧ (((p3 ∨ (p4 ∧ (((((p2 ∧ (p4 ∧ p5)) ∨ False) → False) ∧ p4) ∧ p2))) ∧ p4) ∨ (True ∨ p2))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138348015916339778906449043686 : ((p4 → ((True ∧ ((True ∧ (p2 ∨ (p4 ∧ (((p4 ∧ p2) ∧ True) ∨ False)))) ∧ ((False → p4) ∧ (p4 ∨ False)))) ∨ p2)) ∨ ((p1 ∧ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135359259661113541497120280305 : (((True → ((p5 ∨ (p5 ∨ False)) ∨ ((True ∨ p5) → ((p2 ∨ (True → (p3 ∨ p4))) → p5)))) ∧ (p1 ∨ (True ∨ False))) ∨ (True ∨ (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181360270373852832135253698457 : ((False ∨ (True ∧ ((True ∧ ((p4 ∨ True) ∧ p5)) → ((p2 ∧ False) → p5)))) → (((False ∨ True) ∧ p5) → ((p1 → (p2 ∧ (True → p3))) ∨ p5))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315165442085199282755955936690 : (p3 ∨ (((p4 ∧ p5) → ((p4 ∧ p4) → True)) → (((p4 → p3) ∨ (((p4 → (True ∧ p5)) ∧ (True → (p4 ∧ p5))) → (p5 ∨ False))) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_949189711033109840990754874214 : (((((p1 → False) ∧ p1) ∧ (((p5 ∨ p2) → (p4 ∨ ((p2 → (True → (((p2 → (p5 ∨ p4)) ∨ True) → True))) → p5))) ∨ (p4 ∧ p4))) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h7 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h8 := h4 h7
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h12 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h13 := h4 h12
    -- False on the left can always be used.
    apply False.elim h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341706356708466038670572405618 : (p2 → (((((p5 ∨ p5) → ((p5 ∨ p5) → ((p2 ∧ (p4 ∧ True)) ∧ True))) → (p5 ∨ p4)) ∨ ((p4 ∨ (p5 → p2)) ∨ p3)) ∨ (p1 ∧ p4))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341670814854235270233507722672 : (p2 → ((((p1 ∨ ((True ∨ ((p5 ∧ True) ∧ p3)) ∧ (((p3 ∧ (p3 ∧ p3)) ∨ (p3 ∧ (p2 ∨ p3))) ∨ p1))) → False) ∨ p2) ∨ (p5 → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64071227253224686359272451939 : ((False ∨ ((p5 → ((((p5 → False) → p3) ∨ p5) → (p1 ∨ (((True ∨ p3) → p1) ∧ False)))) ∨ ((((p3 → True) ∧ p2) ∧ p5) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_846265160628822011763653750265 : (((((True ∨ p3) ∧ ((p2 ∧ ((False ∧ (p4 ∨ p5)) → p4)) ∧ (p2 → (((True ∧ (True ∨ p3)) ∨ True) ∧ ((p4 → True) → False))))) ∨ p5) → p5) ∧ True) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h4.left
      let h7 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h10 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h8
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h11 := h7 h10
      -- We need to get the right conjuct of h11 based on <expert-advice>.
      let h12 := h11.right
      -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
      have h13 : (p4 → True) := by
        -- Implications on the right can always be decomposed.
        intro h14
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h12, we can now drive its conclusion.
      let h15 := h12 h13
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h4.left
      let h18 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h19 := h17.left
      let h20 := h17.right
      -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
      have h21 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h19
      -- We have shown the premise of h18, we can now drive its conclusion.
      let h22 := h18 h21
      -- We need to get the right conjuct of h22 based on <expert-advice>.
      let h23 := h22.right
      -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
      have h24 : (p4 → True) := by
        -- Implications on the right can always be decomposed.
        intro h25
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h23, we can now drive its conclusion.
      let h26 := h23 h24
      -- False on the left can always be used.
      apply False.elim h26
  case inr h27 =>
    -- One of the premise coincides with the conclusion.
    exact h27
  -- True on the right can always be proven directly.
  apply True.intro



