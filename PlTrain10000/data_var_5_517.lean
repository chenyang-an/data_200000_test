variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299115518551828890998251809455 : (False ∨ (((p3 ∨ ((p1 ∨ (((p3 → p5) ∨ p1) → False)) → (p3 → ((True → (True ∧ (p4 ∨ ((p1 → False) → p4)))) → p5)))) ∧ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55038624419642602565864706228 : (((p4 ∧ (True ∧ (p2 ∧ (p4 ∨ False)))) ∧ (((p5 → p3) ∨ (p4 ∨ (p1 ∧ (p2 ∨ (p2 → p1))))) ∧ (p1 ∨ ((True ∨ False) ∨ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136159496452713185856197618192 : (((True ∨ ((True ∧ ((p2 → p4) ∧ p2)) → False)) → ((((p5 ∨ False) ∧ p4) → p4) → (((p2 → p1) ∨ True) ∨ p3))) ∨ ((p5 ∧ p5) ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114796372141234039840683013728 : ((((((((p1 ∧ True) → p3) ∧ True) → p5) ∨ p2) ∧ ((p3 ∨ p2) → p5)) ∧ (False ∨ (((p3 → p4) ∧ (p1 ∨ p2)) ∨ p2))) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328274088048679758324006269087 : (True → (((((p5 ∨ ((False → p5) ∧ p2)) ∨ ((p1 ∧ p2) ∨ ((p4 ∧ (p5 → p5)) ∨ True))) ∨ p5) ∨ False) ∨ (True ∨ ((p3 ∧ p5) ∧ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260574785433003669910577911877 : ((p3 → p1) → (p1 → (((p5 → ((p3 → p5) ∨ p3)) → (p4 ∧ (((False ∨ p4) ∧ (p1 ∨ (p1 ∧ False))) ∧ p3))) ∨ ((p2 → True) → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_629103497726611418073182250400 : (((((((p5 ∨ (p4 → (((False → True) → False) ∧ ((p4 ∨ (((p4 ∧ p3) ∨ (True ∨ p1)) → p5)) → p5)))) → True) ∨ p4) ∨ p5) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_779342421635373102404095072413 : (((p2 ∨ ((p2 → ((False ∨ (((p5 ∧ p1) → p2) → ((((p5 → True) → False) ∨ ((False → (p1 ∨ p2)) ∧ p1)) ∧ p1))) ∨ p1)) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_764777796936846685025591554710 : (((p4 ∧ (((p2 → ((True ∨ False) ∧ (True ∨ (((p5 → p5) → p5) → ((((True → p3) ∧ (p4 ∧ p4)) → p3) ∨ p1))))) ∧ True) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_733777400944175881824707173417 : ((((p5 ∧ p3) ∧ ((((p1 ∧ p4) ∧ (p3 ∨ ((True ∧ True) ∧ p1))) → (((p2 ∧ p4) → p5) ∨ ((True ∧ (True ∧ p5)) ∨ True))) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322372912156155413947115955576 : (p5 ∨ ((((p3 → (((p3 ∨ p2) ∧ p5) ∨ p5)) ∧ ((p2 ∧ ((p2 ∨ p2) ∨ p1)) → (p5 → p1))) ∨ (p3 ∧ (p5 ∨ (p3 ∨ p5)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3172734562581248538491911130 : ((p5 → p5) ∧ ((((False ∧ p5) → p3) → (False ∨ p1)) ∨ (((p3 ∧ (((p3 ∧ p3) ∨ p1) ∧ p1)) ∨ p1) ∨ ((p5 → p5) ∨ p4)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204532187793005297080372651420 : (((((p4 ∧ p1) → True) → p4) ∨ p2) ∨ (((p5 ∨ ((p2 ∨ (False → p1)) → (p1 ∨ p5))) ∧ (((p4 → True) ∨ p3) → True)) → (p1 ∨ p5))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : (p2 ∨ (False → p1)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- False on the left can always be used.
      apply False.elim h7
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h6
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
      -- One of the premise coincides with the conclusion.
      exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39410929362080525455618882043 : (((p4 ∧ (((True ∨ ((p2 ∨ (p1 → True)) ∨ p1)) ∨ (False → (p1 ∧ False))) → (p5 ∨ ((p5 → ((p1 ∧ p4) ∨ p4)) → p1)))) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336326631489077030242345479544 : (p1 → (((p3 → (p3 ∨ p5)) ∧ (p5 ∨ (((p4 ∧ (False ∨ p4)) ∨ p3) ∨ ((((True ∧ (p5 → p2)) ∨ True) ∧ True) ∨ (True ∧ p1))))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47803447267608716568159138724 : ((((((p1 → (((p5 ∨ (False → False)) ∧ (p1 ∧ p1)) ∧ p5)) → (p3 → (True → (p5 → p5)))) ∧ (p3 → p5)) → p4) → (False ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694130505137213955398049432117 : ((((((p1 → ((False ∧ p3) ∨ p4)) → False) ∧ (True → (p3 ∨ (p2 → p1)))) ∨ (((p5 ∧ (True ∧ (p1 ∧ p2))) → p2) ∨ (p1 ∧ True))) ∨ p2) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321547553548880054805902567777 : (p4 ∨ (p2 → (((p5 ∨ (((False ∧ p4) ∨ False) ∨ ((p5 ∨ p5) ∨ True))) → ((((p3 → p4) ∧ False) ∧ p2) ∧ (p4 ∧ p2))) ∨ (p1 → p2)))) := by
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
theorem thm_5_vars_681996300119961444876585857306 : ((((((p2 ∨ ((p2 ∧ False) ∧ p5)) ∨ ((p1 ∨ True) ∧ (True ∨ ((p1 ∨ p1) ∧ p4)))) ∨ p2) ∧ (((p4 ∨ p4) ∨ True) ∨ (False ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137510289209800281970748628537 : ((p5 ∧ (((p1 ∨ ((p1 ∨ (p1 ∨ (p1 ∨ p5))) ∧ p3)) → p2) → ((p3 ∨ (p4 ∨ (p3 ∧ p1))) ∨ (p3 ∨ p5)))) ∨ ((True → True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703028344485503300815751121936 : (((((p3 ∧ p4) ∧ (False ∨ (p2 ∨ ((False → p2) ∧ True)))) ∨ ((p1 → ((p2 ∨ p5) → ((p2 ∨ False) → p3))) ∨ ((True ∨ p2) ∨ True))) ∨ False) ∧ True) := by
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
theorem thm_5_vars_50261846659425924787076391196 : ((((p5 → ((True → (p5 → (((p2 ∨ p4) ∨ (False ∧ (p3 ∧ p1))) ∨ (p1 → p1)))) → p2)) → p1) ∨ ((p5 ∧ p2) → (p1 → p2))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158972963682700042811095846252 : ((p3 ∨ ((((True ∨ (((p4 ∨ p5) ∨ (p2 ∨ p4)) → p2)) → ((False → p2) ∨ False)) → True) → p4)) ∨ (p1 ∨ (True → ((p1 ∧ p3) ∨ True)))) := by
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
theorem thm_5_vars_40532384614095688744359497463 : ((((p2 ∨ ((((p4 ∨ p5) ∧ ((True ∨ (p2 ∧ (((p1 → (p2 → p1)) ∧ p3) → p3))) → (p2 ∧ p2))) ∨ p3) ∧ p5)) ∨ True) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150032759250529285374427028701 : ((p5 ∨ (True ∧ (True → ((p4 → (p2 → p1)) ∨ ((False ∧ False) ∨ (((False → p3) → (p3 → p2)) ∨ True)))))) ∨ ((True → (p3 ∨ p4)) → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_115470753428282358417417865261 : (((p2 ∨ (((p4 ∨ (p3 ∧ p4)) ∧ p3) → False)) ∨ ((p3 ∨ True) → ((p5 ∨ (False → ((True ∧ p4) ∧ (p3 → p5)))) ∧ p1))) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55446687967882571293356096087 : (((((p3 ∨ p1) ∨ (p2 ∨ p4)) → p4) → ((p3 → ((p4 ∨ (((p1 ∧ p3) → p4) → (p4 ∨ p5))) ∨ p1)) ∨ ((False ∨ p3) ∨ p3))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((p3 ∨ p1) ∨ (p2 ∨ p4)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141763481816452056691270343108 : (((p3 → p2) ∧ (p2 ∧ (((((((p2 ∨ p3) → p1) → p1) → (p2 ∨ (p2 → p4))) ∧ p2) ∨ p2) ∧ (p4 → p2)))) → ((p4 → True) ∧ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204237059024339446080233694544 : ((((p3 ∧ p2) ∧ (p3 ∨ p4)) ∧ False) ∨ (((p4 ∧ ((p3 ∧ True) ∧ ((((p3 → (p5 ∧ p2)) ∨ True) → (p3 ∨ p3)) ∧ p2))) → True) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47412071986303966885557771080 : (((False ∧ ((p2 → (((True ∨ True) ∧ p2) → True)) → ((p1 ∧ True) ∧ ((p4 → (p3 ∧ False)) → ((p4 ∨ p3) → True))))) ∨ (p1 ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174362351652305105367256834100 : (((False ∨ (((False ∧ ((p5 ∧ True) ∧ p1)) ∧ False) ∧ p2)) → (p5 ∧ (p4 ∧ p3))) → ((p2 → p3) → ((False ∨ (False ∨ (p3 ∧ p1))) → p3))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- One of the premise coincides with the conclusion.
      exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_806223669663503642883397593934 : (((p4 → ((((((p4 → ((((p2 ∧ p2) ∧ False) ∧ False) ∧ True)) ∧ (p2 → p5)) → ((False → p1) → p1)) ∨ True) ∨ (p1 ∧ p3)) ∨ p1)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146814992817831155330183971148 : ((p4 → (((True → p4) → (False ∨ (((((p2 ∨ False) ∧ p1) ∨ (p3 ∧ p2)) ∧ (p1 ∨ False)) ∧ p2))) ∨ True)) ∧ (((p2 → p3) ∧ p1) → p1)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_787722512580539473641833467534 : (((p4 ∨ (p5 ∨ (False ∧ (((p5 ∨ p5) ∨ p3) → (((p5 → p2) → (p5 ∨ p4)) → ((((p2 ∧ True) → p5) ∨ p5) ∧ (p4 ∧ p3))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164756623962998059323100626922 : ((((((p4 ∨ (p5 → p3)) ∨ p3) → (p3 → (p1 ∨ p3))) ∧ ((p4 ∧ p2) ∧ p1)) ∨ p5) ∨ (p3 → (True ∨ ((p1 ∨ p2) ∧ (p1 → p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_706056769633997236293511027824 : (((((p3 ∧ True) ∨ (p4 ∨ (False → (p3 ∧ True)))) ∧ (((p1 → True) ∧ ((False → (True → (((p2 → False) → True) ∧ p1))) → p4)) ∨ True)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138411176176363717797375216764 : ((p5 → ((((p1 → ((False ∨ p1) → p4)) ∨ (p5 ∨ ((p1 → (p5 ∧ p2)) ∨ (p3 ∧ (p5 ∨ p4))))) → p1) ∨ p5)) ∨ (False ∨ (p1 ∨ p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336180450746521694369293157748 : (p1 → (((False → ((((p5 ∨ (p2 ∧ ((((True ∨ p2) ∧ p3) → p5) → True))) ∧ p4) → ((p4 → True) → (p2 ∨ p2))) ∧ False)) → p3) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256410895658264707316159932460 : ((False ∨ p3) → (((((p3 ∧ (p5 ∨ (p4 ∧ True))) → True) → ((False ∧ (p1 ∧ (p5 → p1))) ∨ p2)) ∧ (p4 ∧ p3)) ∨ ((True → False) ∨ p3))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249059835058476090575972345146 : ((p4 ∨ p1) ∨ ((p4 → (((((False ∨ (((False → p1) → p3) ∧ p3)) ∧ p5) ∨ (False ∨ p5)) ∧ ((False ∧ p4) ∨ p3)) → False)) ∨ (True ∧ True))) := by
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
theorem thm_5_vars_190272580082521219192349495532 : (((((p3 ∨ False) ∨ (p2 → (p3 ∧ False))) ∨ p2) ∨ True) ∨ (p5 → (((((p2 → ((p1 ∧ (p5 → p5)) → p2)) → True) → p1) → p2) → False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299274217234913950150330367228 : (False ∨ (((p2 ∧ (((True ∧ (p5 → (False ∨ ((p5 → p3) → (False → True))))) ∨ True) ∨ p4)) → (p5 → ((p1 → p3) ∧ (p2 ∧ p3)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624948267400743822971119413218 : ((((p5 ∨ (p1 ∧ (((False → True) ∧ (p4 ∨ (((p1 ∨ p4) ∧ (p5 ∨ p3)) ∨ (False ∧ (p1 ∧ (p2 → True)))))) → (p4 ∧ p4)))) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_324198464052296875430998993032 : (p5 ∨ (((((p1 → (p4 ∨ True)) ∧ p4) ∨ p1) → (p2 ∧ p4)) → ((((p4 ∨ True) ∧ p1) ∧ (p5 ∨ ((p2 ∨ p4) ∧ p3))) → (True ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    cases h4
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h12 =>
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h13 =>
        -- One of the premise coincides with the conclusion.
        exact h13
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h15 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h16 : (((p1 → (p4 ∨ True)) ∧ p4) ∨ p1) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h17 := h1 h16
      -- We need to get the right conjuct of h17 based on <expert-advice>.
      let h18 := h17.right
      -- One of the premise coincides with the conclusion.
      exact h18
    case inr h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h19.left
      let h21 := h19.right
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h22 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h23 : (((p1 → (p4 ∨ True)) ∧ p4) ∨ p1) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h6
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h24 := h1 h23
        -- We need to get the right conjuct of h24 based on <expert-advice>.
        let h25 := h24.right
        -- One of the premise coincides with the conclusion.
        exact h25
      case inr h26 =>
        -- One of the premise coincides with the conclusion.
        exact h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150089168003645794257501623523 : ((True → (p1 → ((((p2 ∧ p2) ∧ True) ∨ (p4 ∧ (True → (((p4 ∨ True) → p5) ∨ (p2 ∨ p2))))) ∨ True))) ∨ ((p5 ∨ True) → (p5 ∨ p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_802402249605117623297340945615 : (((p2 → (False ∨ ((True → False) ∨ ((p5 ∧ ((p4 ∨ (p1 ∨ p1)) ∧ True)) ∨ ((False ∨ (False ∧ (p4 ∨ (True ∧ (p1 → p1))))) ∧ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303757485300341485824733312382 : (p1 ∨ ((((False ∨ ((p1 ∨ p2) ∨ (p3 → (((p1 → p1) → p4) → (((p5 → False) → p2) ∧ (p4 ∨ p3)))))) → (p2 ∧ False)) ∨ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138070793465806046395759985488 : ((True → (p3 → (p2 ∧ ((((((False → p2) ∧ p4) ∨ (False → p3)) → (False → (p5 ∨ p3))) ∨ (p4 ∧ p5)) → False)))) ∨ (True ∨ (p4 ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218080618226595806232278296567 : (((p5 ∨ p4) ∧ (p4 → True)) → ((p2 → False) ∨ (((True ∧ True) ∨ ((False ∧ ((p2 ∨ ((False ∧ p3) ∨ p1)) ∨ p2)) ∨ (p2 → p1))) ∨ p4))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709431320671597289838186017974 : ((((p2 ∧ (((False ∧ (p5 ∨ p2)) → p4) ∨ p1)) → ((p1 ∨ ((p3 ∧ (True → (p2 → ((True ∧ (False → p5)) ∨ False)))) ∧ True)) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229614173991432035821100645506 : ((p3 → (p5 ∧ p4)) ∨ (((p1 → p5) → (p4 ∨ (True ∧ (p3 → True)))) → ((p5 ∨ ((p3 ∨ (True ∧ p5)) ∨ (p5 → p5))) ∨ (p3 ∧ p1)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134531957699681451300881436751 : ((((((True ∧ (((p2 → (p4 ∧ p4)) ∨ ((p3 ∧ ((p2 ∨ p3) → True)) ∨ False)) ∨ p1)) ∨ False) → p2) → False) → p1) ∨ ((False ∧ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180129319119954820130237974899 : (((((((p3 → p4) ∧ (p3 → p2)) → (p2 ∨ True)) → p3) → p5) → True) → (p3 → ((p1 ∨ p4) ∨ (((p1 ∨ False) → (True ∧ p3)) → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306409493045498675279983407530 : (p1 ∨ ((p2 ∧ p1) ∨ ((p5 ∨ ((p5 → (p2 ∨ p2)) ∧ ((p2 → True) ∨ p1))) → (((((False ∨ p4) → p1) ∨ p2) ∨ p2) ∨ (False → False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- False on the left can always be used.
      apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_21700143841830759254104104964 : ((((True ∧ (True ∧ p5)) ∧ ((p4 ∧ (True ∨ p2)) ∨ True)) → (((((True → p3) ∨ p4) → True) → True) → ((p1 ∧ (p5 → p3)) ∨ p5))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h14 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_725570609262049734375104469606 : (((((p2 ∧ p1) ∧ p2) ∨ (((True → ((((True ∨ False) ∨ p2) ∨ p5) → (False → p5))) ∧ p4) ∧ (((False ∨ True) ∧ p1) ∧ (p4 ∧ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317760595649723397088295167461 : (p4 ∨ (((((((((p5 ∨ True) → p4) ∧ p1) ∧ p4) ∧ p2) ∨ ((False → p3) ∨ False)) ∨ True) ∨ (((p4 → p1) → (p4 ∨ p5)) → p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248868421217564931159719727364 : ((p3 ∨ p5) ∨ ((True → (((p5 ∧ p2) → ((p2 → ((p5 ∧ p3) → p3)) → (p4 ∧ p3))) ∨ ((((False ∧ False) ∧ p1) → p2) → p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254489236830686365642921959680 : ((p3 ∧ True) → (True ∧ (True ∧ ((p2 ∨ (((False → ((((p2 → True) ∧ ((p1 ∨ p2) → True)) → p3) ∨ (p4 ∧ p3))) ∧ p3) → p1)) ∨ p3)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165271442443364175645651711913 : (((((False ∨ ((p4 ∨ (p2 → p1)) ∨ (p3 ∨ True))) ∧ (p4 ∧ p1)) → p5) → (p5 → p5)) ∨ (((p5 → (p3 ∧ True)) ∨ p4) ∨ (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59016765474852262616764887053 : (((p3 ∧ p4) ∨ (p3 ∧ (False ∨ (((True ∧ p2) ∨ (p1 → ((p4 ∨ ((p1 ∨ ((True ∨ p4) ∧ False)) ∧ p3)) ∨ p2))) ∨ (p5 → p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231500155063452732912890174563 : (((p3 → p5) ∨ False) → ((((((False ∧ (p1 ∨ True)) → p5) → (p1 → ((p1 → p1) ∨ p1))) ∨ p4) → ((p2 ∧ p5) ∨ True)) ∨ (p1 → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
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
theorem thm_5_vars_868545994208354903575081426703 : ((((True ∧ ((((False ∧ ((p1 → p2) → False)) ∨ (p4 → (p3 ∧ ((p1 ∨ p4) ∨ ((p4 → p3) ∨ (False ∨ True)))))) ∧ True) ∨ True)) → p3) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∧ ((((False ∧ ((p1 → p2) → False)) ∨ (p4 → (p3 ∧ ((p1 ∨ p4) ∨ ((p4 → p3) ∨ (False ∨ True)))))) ∧ True) ∨ True)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322252368701346953926228481644 : (p5 ∨ ((((False ∧ ((p4 ∨ (((((False ∨ p5) ∧ True) ∧ p1) → True) ∨ p5)) ∧ (True ∧ p1))) ∨ ((p1 ∧ p1) ∨ (p3 ∨ p3))) ∨ True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_773988293794141770923589566052 : (((False ∨ ((((p3 → p1) → ((True ∧ p1) ∨ (((p1 ∨ (p5 → p4)) ∧ p1) → p2))) ∧ ((True ∧ (p5 ∨ p3)) → p4)) ∧ (p3 ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172526462411920888048789587404 : (((False ∨ (p4 ∨ p3)) ∧ (p5 ∧ (p5 ∧ (p4 ∧ ((p3 ∨ False) → (p4 ∧ False)))))) ∨ (p1 → (p4 ∨ (True ∨ (False ∨ ((p1 → True) ∧ p2)))))) := by
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
theorem thm_5_vars_323271834458942869358900171844 : (p5 ∨ ((True → ((p5 ∧ ((p3 ∧ (((False ∨ ((False → p1) ∧ p3)) ∧ ((True ∨ (p2 ∨ p3)) → p1)) ∧ p3)) → p2)) ∧ False)) ∨ (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117573632113669692900277803374 : ((p2 ∧ ((p1 ∧ p3) ∧ ((p3 → (((p3 → ((p5 ∨ p4) ∨ p4)) ∧ (((p5 ∨ (p3 ∨ p2)) ∨ True) ∧ p4)) ∧ p5)) ∧ p4))) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136059979958239984618140890635 : ((((p2 ∧ (True ∨ (p3 → (p1 ∧ False)))) → p3) ∧ (((p3 ∧ True) ∨ (True ∨ (p4 ∧ (True → (p1 → False))))) ∧ p5)) ∨ ((p2 ∧ False) → p4)) := by
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
theorem thm_5_vars_161203851203348011012551624527 : (((False → True) ∨ (((p2 → p4) ∨ p4) ∨ ((((p1 → False) ∨ (p2 ∧ (p3 ∧ False))) ∧ p3) → p5))) → (True ∧ (p5 ∨ (p3 → (True ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h7
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h9
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_766514265261841582765368407878 : (((p4 ∧ (p3 ∧ ((((p5 ∨ (p5 ∧ (p4 → ((p5 ∨ p2) ∨ p4)))) ∨ p1) → ((((p3 ∨ (p1 ∧ False)) ∧ True) → p3) → p1)) ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47327000863622055040865406889 : ((((p4 ∨ (p2 ∨ False)) → (False ∨ (((p2 ∧ p5) ∨ False) ∨ ((True ∨ (p5 ∨ ((p2 → True) ∧ (False → p2)))) ∨ p1)))) ∨ (False ∨ p5)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
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
    case inr h5 =>
      -- False on the left can always be used.
      apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231464462024232310442249850575 : (((p2 → p5) ∨ p4) → (p4 ∨ (((True ∧ (False ∧ (((p1 → p4) → ((p5 ∨ p2) ∧ True)) ∧ ((p5 → p5) ∨ False)))) ∧ True) ∨ (True ∨ True)))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304006504143633133096115607385 : (p1 ∨ (((p4 ∨ True) → ((((True ∧ False) ∨ p3) → p3) → ((p1 → p4) ∨ (True → ((p1 ∨ p5) → (True ∨ (p3 → (p5 ∨ p4)))))))) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116670188225986408837871523574 : (((p5 → True) ∧ (((True ∧ ((True → False) ∧ (True ∧ p1))) ∨ False) ∧ (p3 ∧ (p3 ∧ (p2 → ((False ∨ p2) ∨ (False ∨ p1))))))) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310781801113814623634623066076 : (p2 ∨ (((True → False) ∨ p3) ∨ ((True ∧ (((p2 → ((p5 ∨ (p5 ∧ p1)) ∨ ((p1 ∧ (p1 ∨ p5)) ∧ False))) ∨ (False ∨ True)) ∨ p3)) ∨ p3))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48745947542671269636173218441 : ((((p2 ∨ (p4 → True)) → (((p5 → ((p2 → ((p4 ∨ p3) ∧ (True ∨ (p3 ∨ p3)))) ∧ p2)) ∧ False) ∨ False)) ∧ ((False ∨ False) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135271161739142791942284536873 : (((p1 ∨ (p5 ∧ (((p2 ∧ (((True ∨ False) ∧ False) ∨ ((p1 ∨ p4) ∧ (p1 ∧ p1)))) → p3) ∨ p3))) → (p1 ∧ p1)) ∨ (True ∨ (True ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148657372005448278416305285616 : (((True ∧ (((p3 → p3) → (p5 ∨ p1)) ∨ p3)) ∧ (False ∨ (p2 → ((p5 ∧ ((p5 ∧ False) ∨ p5)) → p3)))) ∨ (((True → False) ∧ False) → p2)) := by
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
theorem thm_5_vars_337973787736159337118818563787 : (p1 → ((((p1 ∨ ((p2 ∧ p3) ∧ (p5 ∨ True))) → (p4 → p3)) → p2) → (p2 ∨ ((p1 ∧ (True ∧ p4)) ∨ ((p2 → p3) ∨ (p2 ∨ True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
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
theorem thm_5_vars_115932546158759264196148897107 : (((p2 ∧ (True → (p3 ∨ p5))) ∨ (((False → (True ∧ (p4 ∨ (p2 → p2)))) → (True → p4)) → ((True ∨ (p1 → p1)) → p4))) ∨ (p3 ∨ p5)) := by
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
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h4 : (False → (True ∧ (p4 ∨ (p2 → p2)))) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- False on the left can always be used.
      apply False.elim h5
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h6 := h1 h4
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h8 := h6 h7
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h10 : (False → (True ∧ (p4 ∨ (p2 → p2)))) := by
      -- Implications on the right can always be decomposed.
      intro h11
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- False on the left can always be used.
      apply False.elim h11
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h12 := h1 h10
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h13 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h14 := h12 h13
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172451749216378130059995377419 : ((((p5 → True) ∧ (p3 ∨ p2)) ∨ (((((p5 ∧ p5) ∧ p1) → p2) → p3) ∧ p4)) ∨ (((((p5 ∧ (p4 ∨ p3)) → p4) ∧ p2) ∨ True) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346236744230319378246273027590 : (p3 → (((p2 ∧ (p5 ∨ p2)) → (((p5 ∨ ((True → (p2 → False)) ∨ False)) ∧ p4) → ((p1 ∨ p4) ∨ ((p4 ∨ p3) ∨ p3)))) ∧ (p4 ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h2.left
    let h8 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h2.left
      let h14 := h2.right
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h16 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
    case inr h17 =>
      -- False on the left can always be used.
      apply False.elim h17
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234113544242407065146481469212 : ((True → (False ∨ p5)) → ((p4 ∨ (False ∧ p4)) ∨ (p4 → ((p5 ∧ p5) ∧ ((((p5 ∨ p1) ∨ p2) → ((p1 → False) → (p4 ∨ p4))) → p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h5
    -- One of the premise coincides with the conclusion.
    exact h5
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191490740823486430238231393466 : ((True ∧ (p4 ∧ ((p5 → (p2 ∨ p3)) ∨ (p5 ∧ True)))) ∨ (((((((p4 ∧ (p1 ∧ True)) → False) ∧ p5) ∧ (True ∨ p5)) ∨ False) ∨ True) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41068880897631672825494819692 : ((((p2 ∨ ((p2 → (p2 ∨ (p5 ∨ p2))) ∧ ((p3 ∧ p5) ∨ ((p3 → True) ∧ (((True ∨ True) → p3) → p3))))) → (p2 ∧ p3)) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257143735588566008740208140665 : ((p2 ∨ p1) → (((p1 → (p4 ∧ (p3 → ((p5 ∨ (p3 ∧ p3)) ∧ (False ∧ (p3 ∧ p4)))))) → p5) ∨ ((False ∧ (p5 → (p5 ∧ p1))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324648824578396893292369816715 : (p5 ∨ (((p2 ∨ False) ∨ p1) ∨ ((p2 ∨ ((p4 ∧ p3) → ((p1 ∧ p4) → ((((p1 → p4) ∧ p3) ∨ False) ∨ False)))) ∨ ((p4 ∨ p1) ∧ p4)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h7
  -- One of the premise coincides with the conclusion.
  exact h5
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_595974778999957173052933644003 : (((((p4 ∨ ((True → ((True → (p1 → p2)) ∧ p1)) → p5)) ∨ (p1 ∧ ((p5 ∨ p3) ∧ (p2 ∧ (p5 → ((p2 ∧ p5) ∨ p1)))))) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321069620563641850607536266246 : (p4 ∨ (p1 ∨ ((p3 ∨ (p3 ∨ ((((p4 ∨ p1) ∧ ((p5 ∧ True) ∧ (p3 → p1))) ∧ p1) ∧ p2))) ∨ ((p4 ∨ (p2 ∨ p4)) ∨ (False → p4))))) := by
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
theorem thm_5_vars_62474656490041424602921650472 : ((p3 ∧ ((p2 → p3) ∨ ((((p1 → (p2 ∧ p2)) → (p2 ∨ (p2 ∨ (False ∨ True)))) → False) → (((p3 ∧ p3) ∧ (p3 → p3)) ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_626420383649827985421766460016 : ((((p4 → (((((((p2 → ((p4 ∧ (True ∧ False)) ∨ p5)) ∧ (p1 ∧ (p5 → (p1 → p1)))) ∨ False) ∧ False) ∨ p5) ∧ p1) ∨ False)) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_46077632824588765312533245887 : ((((((False → p2) ∧ (True → ((p5 → ((p5 ∧ True) ∧ True)) ∨ ((p4 ∧ p4) ∧ (p1 → p1))))) → (False ∨ p1)) ∨ True) ∧ (False → True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45449400664814970658901129840 : (((True ∨ ((p5 → p2) ∨ (p4 → (((p1 ∧ ((p4 ∨ True) ∧ p5)) ∨ ((p1 → p4) ∨ p5)) ∨ ((p4 → (p3 ∧ p3)) → p5))))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354886129943894764654464497885 : (p5 → ((p2 ∧ (p5 ∧ (p3 ∧ ((p1 ∨ p5) → (((False → (p3 ∨ p1)) → ((((p3 ∨ p4) → p5) → p4) ∨ (p4 → p3))) ∨ p4))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165000303391969349239962171259 : ((((p4 ∨ (True ∧ (True ∧ ((p1 ∧ p2) ∨ p3)))) ∨ (True ∨ (True ∨ (p3 → p2)))) → p2) ∨ ((False → ((True ∨ p2) → True)) → (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52004862575116100501038862848 : (((p2 ∧ ((((p4 ∧ ((False ∧ (False → p1)) ∨ (p1 ∨ p3))) → False) ∧ True) ∧ p4)) ∨ ((((p3 ∧ p2) ∨ False) → p2) ∨ (p5 → p1))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704618043819585023888201796956 : (((((p3 ∨ True) → (p1 ∨ ((p5 ∧ (False ∧ p5)) → p4))) → (((p4 → ((False → (p4 → p2)) ∨ (False ∨ (True → p1)))) ∨ p4) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113274264482515581318772796895 : ((((((((p3 ∨ (p1 ∨ p2)) → p3) → False) → p2) ∧ (True → (True ∨ p4))) ∨ (((False → True) ∧ p4) ∨ p1)) ∧ (False → p4)) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262345384857323067233063780608 : (True ∧ ((((True → False) ∨ (p4 ∨ p5)) ∨ ((p3 ∨ p2) ∨ (((p2 ∨ p2) ∨ (((p3 ∨ (p4 → p4)) → p1) ∨ p1)) → (p2 → False)))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



