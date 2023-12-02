variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40882159513975155806756919445 : (((((((p5 ∧ p2) ∨ (p3 ∨ p3)) → (((p4 ∧ p2) ∧ p3) ∧ (True → False))) → (((p5 ∨ p3) ∧ p4) ∨ True)) ∧ (True → True)) ∨ p3) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133719130843106688413648309685 : ((((p4 ∧ (((p1 → (p4 ∧ p3)) ∧ ((p2 ∨ p5) → p5)) ∨ True)) ∧ (p1 ∨ (((False → False) ∨ False) ∨ False))) ∧ p1) ∨ ((p3 ∧ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780808174475542378763127371310 : (((p2 ∨ (((p4 ∧ (p4 ∨ False)) ∧ p3) ∨ (True ∨ ((p3 ∧ False) ∧ (p1 ∨ (((((p4 → (False ∨ p3)) ∨ p1) ∧ p3) ∨ p3) → False)))))) ∨ p2) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609778669301665711279836924380 : (((((p5 ∨ (((False ∨ (((p5 → (p1 ∨ p5)) → False) ∨ (p4 → False))) ∨ p5) ∨ (p2 → (((False ∨ False) → p4) ∨ p5)))) ∨ p1) ∨ p5) ∨ p5) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324465172290741594501004452452 : (p5 ∨ ((p4 ∨ ((p5 → p5) ∨ p5)) ∧ ((p2 ∧ False) ∨ (p5 ∨ ((False ∨ True) ∧ ((p4 ∨ p5) → ((((p2 ∨ p3) ∨ p2) → p4) → True))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_675191612613141199687179042184 : ((((((False ∧ ((p1 ∧ p2) → p1)) ∧ (((p2 → (p3 ∨ p4)) ∧ ((p4 ∧ False) → p4)) → p1)) ∨ True) ∧ (p2 → ((p4 ∨ p5) ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111952216953509004638619019309 : (((((((True ∨ (p4 ∧ True)) ∧ p2) ∨ p2) ∧ False) ∨ (((p5 ∧ ((p2 ∨ p5) ∨ False)) → (p1 → (p4 ∧ p3))) ∧ True)) ∨ p5) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64246138953939689001651404778 : ((False ∨ (p2 ∨ (((False ∨ ((True ∨ (p5 → ((p2 ∧ p5) ∨ p2))) ∧ (p3 → ((p5 → p1) ∨ p5)))) ∨ False) ∧ (False ∧ (p2 ∧ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56787838702151463895834092546 : ((((p4 ∧ p5) → p5) ∧ (p2 ∨ (True → (((p1 → ((p5 ∧ ((True → p2) → False)) ∨ False)) ∨ (p2 → (False ∨ True))) ∧ (False → True))))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149402745707842099093201148091 : ((True ∧ ((((p5 ∧ p3) ∨ (p3 → p3)) ∧ (True → (((False → p3) ∨ ((p5 ∨ p2) ∨ True)) ∧ p3))) → p3)) ∨ ((p2 ∨ (p2 ∧ p4)) ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h9 := h3 h8
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184344311965095737321533404423 : (((p3 ∧ (((p1 ∧ (p1 ∨ (p3 ∧ p3))) → p2) ∨ p5)) → p4) ∨ (p1 ∨ (p3 → (p5 → ((p2 ∧ ((p4 → (p2 ∧ p2)) → p1)) ∨ True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37804623966723240095738578092 : ((((p1 ∧ (((True → ((p2 → p1) ∧ (p4 ∨ p2))) ∧ False) → ((((p2 → p5) ∨ (False ∧ p1)) ∧ False) → (p4 ∨ p1)))) → p4) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116557709890744019012568551354 : (((p1 ∨ p5) ∧ (((p5 ∧ p3) ∨ (p3 → ((p2 ∨ ((p1 → ((p2 ∨ True) ∨ (p3 ∧ (p3 ∨ p4)))) → p1)) ∨ p1))) ∧ p5)) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227534079231572566178391199061 : ((True ∧ (True → p5)) ∨ (((((p4 ∨ (False ∨ ((((p3 ∨ p5) ∨ p3) ∨ (p2 ∨ p4)) → (p1 ∨ p2)))) ∨ True) ∨ (p5 ∨ p3)) ∨ p4) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136390312409467193855031371829 : (((False ∧ (True → (p2 ∧ p2))) ∨ (p1 ∨ (((p5 → p3) ∨ p4) → ((((p4 ∨ (p5 → p3)) ∨ False) → p5) → p5)))) ∨ ((p5 → False) ∨ p4)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : ((p4 ∨ (p5 → p3)) ∨ False) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h6 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h7 := h3 h6
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h4
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h10 : ((p4 ∨ (p5 → p3)) ∨ False) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h11 := h2 h10
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57088383098018707468497980938 : ((((p2 ∧ p4) ∧ p3) ∨ ((p3 → ((p5 ∧ (((p3 → p4) ∧ p5) → (p5 ∧ p4))) ∨ True)) ∨ ((p2 ∨ p3) ∨ (p2 → (p3 ∧ p5))))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621193087499648767476894548321 : ((((True ∧ (((((((p3 ∨ p5) ∧ p3) ∨ p3) ∧ ((p5 ∨ p1) ∧ ((p1 ∧ (p4 → True)) ∧ p4))) ∨ p1) ∨ (p1 ∨ True)) ∨ p2)) ∨ p2) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348803504181187520238595821702 : (p3 → (p1 ∨ (((p3 → (((p2 ∨ False) ∧ p1) → (p1 ∨ ((((p1 → p4) ∧ p2) ∧ (p1 → p5)) → False)))) → p5) ∨ (False → (True → p2))))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_243785830343242964369247304728 : ((p5 → p5) ∧ ((p5 ∨ ((p2 ∨ (p1 ∧ (p5 ∧ ((p2 ∧ p2) → True)))) ∨ True)) ∧ (((((p2 → p2) ∧ (p5 ∨ True)) ∨ p3) ∨ p4) ∨ False))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656240907399566671709612621067 : (((((p4 ∨ (p3 → ((p1 → (p1 → p3)) ∨ ((p1 ∨ (p4 ∧ p2)) → p5)))) → (p4 → (((p2 ∧ p5) → p2) → p3))) ∨ (p5 ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42137825221648062726771477575 : ((((p4 ∨ True) → ((((((p4 → p3) ∨ p1) → p5) → ((False ∨ (p4 ∨ (p3 ∨ (False ∨ (p1 ∧ p4))))) ∨ p5)) ∨ p3) ∨ True)) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40309715120464475708881106753 : ((((((((p5 ∧ (p1 ∨ p5)) → p4) ∨ ((False → p5) → False)) ∨ (False ∧ (((p2 ∨ (False → True)) ∨ True) ∧ True))) ∧ p2) ∨ p2) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_775846386529568108178493313552 : (((False ∨ (True → ((p4 ∨ ((p1 → (p5 → True)) ∧ (p1 ∧ ((True ∧ p3) → (False → (p2 ∨ p4)))))) ∨ ((p3 → p2) → (p3 → False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314325970747085197792945143314 : (p3 ∨ (((p4 → ((p3 → False) → p4)) → (((True ∨ (p5 → ((True ∨ p5) ∧ p3))) ∧ ((p3 → p2) ∨ p2)) ∨ p4)) → (p4 ∨ (p2 ∨ True)))) := by
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
theorem thm_5_vars_111606068058301979472642983776 : (((((p4 ∨ (p3 → (False ∨ ((((p5 → (False ∧ p5)) → (p5 → p3)) ∨ p2) → ((p4 ∧ True) ∧ p2))))) ∧ p2) ∨ p1) ∨ True) ∨ (p3 → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_242305056050720757205518445920 : ((p2 → p2) ∧ ((((p4 → (p5 → (p3 ∨ (p2 ∨ ((((((p4 ∧ True) ∧ p2) ∧ (p1 ∧ p1)) → p2) ∧ p1) ∧ True))))) ∧ p1) ∨ p2) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41234666887612309008688293391 : ((((p3 ∧ ((True ∧ p1) ∨ (False ∨ (((True → ((p5 ∧ p4) ∧ p3)) ∨ p1) ∨ (p2 → False))))) ∧ (p1 → ((p3 → False) → p4))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264103846691941904287189606819 : (True ∧ ((((p5 ∧ True) → p1) → (p1 ∨ ((p4 ∧ p4) ∧ True))) → ((((p5 → False) ∨ True) ∧ p2) ∨ ((p2 → p5) → ((p2 ∨ p4) ∨ True))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356457924900571870973213186952 : (p5 → ((p4 → ((((p2 ∨ False) ∧ (p2 → (p4 ∨ p2))) → False) ∨ p2)) ∨ (((True → p2) → ((p5 → p3) → p4)) ∨ ((p5 ∨ p5) ∨ p3)))) := by
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
theorem thm_5_vars_48201329213262597826901812491 : ((((False ∧ p2) → (p3 ∧ (p4 ∨ ((((p3 ∨ False) ∨ False) → (p4 ∧ ((p5 ∧ p1) → ((p3 → p3) ∨ p4)))) → p5)))) → (False ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257367964515208715292740220394 : ((p2 ∨ p5) → (((((((True → p2) → p1) ∨ ((p5 ∨ False) ∧ p1)) → (p2 ∨ p3)) → p1) ∨ ((p4 → p3) ∨ ((True ∨ p1) → True))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705030154750259712470991574316 : ((((p2 → ((True ∨ ((p1 → p5) ∧ False)) ∨ (p3 → p2))) → (((p2 ∧ False) → p3) ∧ (p1 ∧ (p4 ∧ (p3 ∨ ((p1 ∧ p5) → p4)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_382789950810523367320772927616 : ((((((p1 → False) ∧ (((p3 → p2) → ((((p2 ∧ (p4 ∨ p1)) ∨ p5) ∧ p3) ∧ False)) ∧ (False ∧ (p2 ∨ (True → p4))))) ∨ True) ∨ p3) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2843939863851586370948541295 : ((p5 ∧ (p2 ∨ (p3 ∧ False))) → ((p4 ∧ (((p1 ∨ p5) → (False ∨ (p4 ∨ ((False → p1) ∨ p3)))) ∨ p5)) ∨ (True ∨ (True ∧ p5)))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184058780028299337545886757668 : ((((True → (False ∨ ((p1 ∨ False) ∨ p3))) ∨ (False ∨ False)) ∨ True) ∨ ((False ∧ (((((False ∧ (p5 ∨ p1)) → p5) → p5) ∧ p4) ∨ p2)) → True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_242147666930338621496252199166 : ((p2 → True) ∧ (((p4 → ((p3 → True) → p3)) ∨ (p4 ∨ (False ∨ p2))) ∨ ((p4 ∧ ((((p4 ∨ p3) ∧ True) ∨ p3) ∧ False)) ∨ (False → True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134531743252695368838480585473 : (((((((p3 ∧ ((((p1 ∨ p2) → p5) ∨ p3) ∧ (p2 ∨ ((False ∨ p5) → p3)))) ∨ p3) ∨ True) → p3) → False) → False) ∨ (False → (True → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117658946396585041748170485939 : ((p3 ∧ ((((False ∧ p4) ∨ (p3 → ((p4 ∨ False) → p2))) → ((((False ∨ False) ∧ p3) ∧ True) ∧ p1)) ∧ (True → (p2 ∧ True)))) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338820520583695228008942348465 : (p1 → ((p4 ∨ False) ∨ ((((p2 ∨ (p3 ∧ False)) ∨ (((True ∧ ((p3 ∧ p1) ∧ (p3 ∨ p4))) ∧ p4) ∧ False)) ∨ True) ∨ (True ∧ (p2 ∧ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699247631052991749403202198888 : ((((p5 → ((((p4 ∨ (p4 ∨ p2)) ∧ (p1 → p4)) ∧ p4) ∨ p4)) ∨ ((((p1 → ((p1 ∧ p2) ∨ p4)) ∧ (False ∨ p3)) ∨ p3) ∨ True)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_174447204011462438249593079368 : ((((p3 ∧ (p2 → True)) ∨ ((True → False) → p4)) → ((p5 → (False → True)) ∧ False)) → ((True ∧ (p4 → p5)) ∨ (p2 ∨ ((p3 → True) → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p3 ∧ (p2 → True)) ∨ ((True → False) → p4)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133987872558354271022003383253 : ((((((((p4 ∧ p2) → ((p2 ∧ ((p4 ∨ p2) → (False ∧ False))) ∧ p3)) → p1) ∨ p1) → (p4 ∧ p5)) ∧ p4) ∨ True) ∨ ((p4 ∨ False) ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_776428621768949783072764438876 : (((p1 ∨ (((p2 ∨ (p3 ∧ ((False → (p5 ∨ ((p5 ∨ p5) ∧ ((p1 ∧ p5) → ((True ∨ p1) → p1))))) ∧ (p5 ∧ p5)))) ∨ p3) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_642878935761710216556686563753 : ((((p2 ∧ ((((p1 ∨ (p5 ∧ False)) → ((False ∨ (p5 ∨ ((True → p2) ∧ p2))) ∧ p2)) → ((p5 → p5) ∧ (p3 ∨ p4))) → p3)) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_787879130001392046527404346859 : (((p4 ∨ (p2 → (True ∧ ((((((p2 ∧ p5) ∧ True) ∨ (p3 ∨ p1)) ∨ (p5 → p4)) ∨ (((p3 → p2) → (p3 → True)) ∧ p5)) ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_189052034674305708173077634262 : ((((True ∧ p3) ∨ p5) → (p1 ∨ ((p4 ∨ p1) ∨ True))) ∧ ((p1 ∨ p2) ∨ (False → (((((p3 → False) ∨ True) ∧ (p3 → p1)) ∨ p1) ∨ p3)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354901231370830455269235355925 : (p5 → ((p5 ∧ ((p5 → (((True → (p1 ∧ False)) ∨ (p3 → p3)) → True)) ∧ ((p4 ∨ (False ∧ True)) ∧ (p2 ∧ ((p2 → p3) → False))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224823776419421235608045245738 : ((p4 → (False → p5)) ∧ (((True ∧ p4) ∨ (p1 ∧ ((p3 ∧ ((p2 → False) ∨ (True → ((p1 ∧ p2) ∧ (p2 ∨ (p3 → p5)))))) ∧ p5))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171549877630462596714950650925 : ((((((p1 ∧ p4) ∧ ((((False → p2) → True) ∨ True) → False)) → p5) → p2) ∨ p2) ∨ (False → (p2 → (p4 ∧ (p1 → (False ∧ (p2 ∨ p5))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148017252801183670734092453198 : (((((p2 ∨ p2) → (((True → (p5 → p1)) ∧ p3) ∨ p5)) ∨ (p5 ∨ (p5 → (p5 ∧ True)))) ∨ (True ∧ True)) ∨ ((p2 → (True ∧ p2)) ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228915760002819810768514308950 : ((p4 ∨ (False ∨ p3)) ∨ ((((p4 ∧ ((p2 ∨ p3) → ((((p4 ∨ p2) ∨ (False ∨ p1)) ∧ p4) ∧ (p5 ∧ p1)))) ∨ (p5 → p3)) ∨ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171421095058371103903809905242 : ((((p2 ∧ p4) ∧ (p3 ∧ (True → (p3 ∧ ((p5 ∨ p4) ∨ (p2 ∨ True)))))) ∧ p3) ∨ (((p3 ∧ (False ∧ (p4 → p5))) ∨ (p1 ∧ False)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264317591717018004978257637288 : (True ∧ ((p5 ∧ (p1 → ((True → True) ∧ p2))) → (p4 ∨ (True ∧ ((((True → ((p4 ∨ (p2 → p2)) → p3)) → p4) ∧ p3) → (p5 ∧ p4)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Conjunctions on the left can always be decomposed.
  let h7 := h4.left
  let h8 := h4.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h9 : (True → ((p4 ∨ (p2 → p2)) → p3)) := by
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h13 =>
      -- One of the premise coincides with the conclusion.
      exact h8
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h14 := h7 h9
  -- One of the premise coincides with the conclusion.
  exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250833491090706789288668723878 : ((p1 → p2) ∨ ((p1 ∨ ((p5 → (p2 → (p3 ∧ p4))) → False)) ∨ (((((True → True) → p2) ∧ ((False ∧ (p4 ∨ p4)) ∨ p1)) ∧ p5) → p1))) := by
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
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_767675372774806949444613950986 : (((p5 ∧ ((p5 ∧ ((((p1 ∧ False) ∨ True) ∧ ((p5 ∧ p4) ∨ ((((p5 → p5) ∨ p3) → False) ∧ p3))) → (p4 → (p1 ∧ p2)))) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117502891138145845522060173502 : ((p2 ∧ (((((False ∨ (False ∨ True)) ∧ ((p3 → True) ∨ p3)) ∧ p4) ∨ (p3 ∨ (((p3 ∨ False) → (False → p3)) → p2))) ∧ p3)) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729604776852203011915400339507 : (((((p5 ∨ False) ∨ p3) → (((p1 → ((p5 → p5) → (p5 → p4))) ∨ ((p2 ∧ (p3 ∨ ((False ∨ p2) → (p4 → p2)))) → p5)) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338077452160009245643141439421 : (p1 → ((p1 ∧ ((p4 ∧ False) → (False ∨ (p1 ∧ (True → p3))))) → (p5 ∨ ((((False ∨ (p1 → (p5 ∨ p4))) ∧ (p1 → p4)) ∨ p1) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152133470701805379028648226058 : (((p1 ∨ (((p1 ∨ (True → False)) ∨ p3) ∨ p3)) ∧ (p4 ∧ (((p2 ∨ (p4 → p4)) ∨ p5) → (p5 ∧ p2)))) → ((p5 ∨ False) ∧ (False ∨ True))) := by
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
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : ((p2 ∨ (p4 → p4)) ∨ p5) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h9 := h6 h7
    -- We need to get the left conjuct of h9 based on <expert-advice>.
    let h10 := h9.left
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h14 =>
          -- Conjunctions on the left can always be decomposed.
          let h15 := h3.left
          let h16 := h3.right
          -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
          have h17 : ((p2 ∨ (p4 → p4)) ∨ p5) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h18
            -- One of the premise coincides with the conclusion.
            exact h18
          -- We have shown the premise of h16, we can now drive its conclusion.
          let h19 := h16 h17
          -- We need to get the left conjuct of h19 based on <expert-advice>.
          let h20 := h19.left
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h20
        case inr h21 =>
          -- Conjunctions on the left can always be decomposed.
          let h22 := h3.left
          let h23 := h3.right
          -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
          have h24 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h21, we can now drive its conclusion.
          let h25 := h21 h24
          -- False on the left can always be used.
          apply False.elim h25
      case inr h26 =>
        -- Conjunctions on the left can always be decomposed.
        let h27 := h3.left
        let h28 := h3.right
        -- We want to use the implication h28 based on <expert-advice>. So we show its premise.
        have h29 : ((p2 ∨ (p4 → p4)) ∨ p5) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h30
          -- One of the premise coincides with the conclusion.
          exact h30
        -- We have shown the premise of h28, we can now drive its conclusion.
        let h31 := h28 h29
        -- We need to get the left conjuct of h31 based on <expert-advice>.
        let h32 := h31.left
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h32
    case inr h33 =>
      -- Conjunctions on the left can always be decomposed.
      let h34 := h3.left
      let h35 := h3.right
      -- We want to use the implication h35 based on <expert-advice>. So we show its premise.
      have h36 : ((p2 ∨ (p4 → p4)) ∨ p5) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h37
        -- One of the premise coincides with the conclusion.
        exact h37
      -- We have shown the premise of h35, we can now drive its conclusion.
      let h38 := h35 h36
      -- We need to get the left conjuct of h38 based on <expert-advice>.
      let h39 := h38.left
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h39
  -- Conjunctions on the left can always be decomposed.
  let h40 := h1.left
  let h41 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h40
  case inl h42 =>
    -- Conjunctions on the left can always be decomposed.
    let h43 := h41.left
    let h44 := h41.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h45 =>
    -- Disjunctions on the left can always be decomposed.
    cases h45
    case inl h46 =>
      -- Disjunctions on the left can always be decomposed.
      cases h46
      case inl h47 =>
        -- Disjunctions on the left can always be decomposed.
        cases h47
        case inl h48 =>
          -- Conjunctions on the left can always be decomposed.
          let h49 := h41.left
          let h50 := h41.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h51 =>
          -- Conjunctions on the left can always be decomposed.
          let h52 := h41.left
          let h53 := h41.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h54 =>
        -- Conjunctions on the left can always be decomposed.
        let h55 := h41.left
        let h56 := h41.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h57 =>
      -- Conjunctions on the left can always be decomposed.
      let h58 := h41.left
      let h59 := h41.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54042897542106731214932632475 : ((((p5 → (p2 → ((True ∨ p4) → p1))) → (True → p2)) → (p4 ∨ (p4 → (((False ∧ p3) → ((p2 → (False ∨ False)) → p4)) → p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60594721461320716513051479593 : ((True ∧ ((True → (((True ∨ True) → False) ∨ (((p4 ∧ (False → p2)) ∧ ((p2 ∧ p1) → True)) → (p3 → ((False ∧ p3) → p2))))) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111850362083222634498668604797 : ((((((p5 ∧ (p1 ∧ (p1 ∨ p5))) ∨ (True ∧ p2)) → ((p2 ∧ p2) ∧ (p3 ∨ (p2 → p5)))) → (True → (p3 ∧ p1))) ∨ True) ∨ (p5 ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53650230440823449455123486610 : (((((p5 → p1) ∧ p4) → (False ∨ (p5 ∨ (True ∨ p3)))) ∧ (False ∨ (p1 → ((p3 ∨ p5) → ((p4 → p3) ∨ ((p2 → p2) ∨ p3)))))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338207728961723234950784501335 : (p1 → ((True ∧ (p3 ∨ (False → (p2 ∨ p4)))) ∧ ((p5 ∨ ((((p1 → (True → p5)) → ((p2 → (p4 → False)) ∧ p5)) ∧ p5) ∨ p1)) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184120333895305825491687907096 : ((((p3 → p5) → ((((p2 → p1) ∨ p2) ∧ True) ∧ p4)) ∨ p2) ∨ (((p2 ∨ ((p2 → False) ∧ (p2 ∧ (False → p3)))) → (False → p1)) ∨ p3)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305884917205102280259999544157 : (p1 ∨ ((p1 ∧ (False ∧ ((p4 ∧ p4) ∨ False))) ∨ (False → (p5 ∧ (((p2 ∨ True) ∨ p2) ∨ ((((p2 ∧ True) → p2) ∧ False) ∧ (p4 → p5))))))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52762340311055268626758330371 : ((((((p3 ∨ p5) → (p5 ∧ p2)) → ((p3 ∧ p3) ∨ (p1 → p1))) → False) → ((p2 ∧ ((p3 → (p1 ∧ (p2 ∧ p4))) → p5)) ∨ p5)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p3 ∨ p5) → (p5 ∧ p2)) → ((p3 ∧ p3) ∨ (p1 → p1))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204660018733625449958400123789 : (((p4 ∧ (p5 ∧ (p3 ∧ p4))) ∨ p4) ∨ ((p3 ∧ p2) ∨ (p4 ∨ ((True → (((False ∧ (p4 ∧ (p1 ∧ True))) → p4) ∧ True)) ∨ (p3 ∧ p3))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347321615050749166289248690887 : (p3 → (((p5 ∧ p2) → ((p3 ∨ (p5 ∧ p1)) ∨ (True ∧ True))) → ((p5 ∧ (p4 ∧ p1)) ∨ (((True → p1) ∨ p3) ∨ ((True ∨ p2) → p3))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_595528542121605925413092456665 : (((((p1 ∨ ((p3 ∧ p4) ∨ (p1 ∧ ((p2 ∨ p3) → (p4 ∧ False))))) ∨ (((True ∨ (p5 ∨ p1)) ∧ ((False → p4) → p5)) → p4)) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259765639277868202598626655030 : ((p1 → p2) → (((True ∧ p2) ∧ p1) ∨ (((p2 → p1) ∧ (p4 → True)) ∨ ((((p1 ∨ (p4 → p1)) ∧ p1) → (p1 ∨ (p4 ∧ p3))) ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_734147247200685902002930078785 : ((((True ∨ p5) ∧ ((p3 ∨ ((p1 → (True → False)) → ((p4 ∧ ((True → p4) → p1)) ∧ p5))) ∧ ((((p1 ∨ p1) ∨ p2) ∧ p1) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_750673801419883581962613212265 : (((True ∧ (((True → p4) → (((False → (((p1 → p3) ∨ p1) → p2)) ∧ p3) ∧ (False → p4))) → (((p2 ∨ (p3 ∧ p5)) ∧ p4) ∨ True))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313107872028992953182674825729 : (p3 ∨ (((((((p2 ∨ p3) → (p3 → (False ∧ p5))) → (p4 → (True ∧ p3))) ∨ (False → (p3 ∧ p2))) ∧ p2) ∨ ((p1 → p5) ∧ True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620240224428883504025376245428 : (((((p5 ∧ False) ∨ (False ∨ ((((p5 ∧ p3) → (p5 → (((((p4 ∧ p2) ∧ p1) ∧ (p5 ∨ p3)) ∧ p5) ∨ True))) ∧ True) ∧ False))) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_748610476472723033868208354523 : ((((p3 → p1) → (p4 ∨ ((p1 ∨ ((False → p1) → p5)) → (True → (((p2 → (p1 ∨ (p4 → p3))) ∨ (p4 ∨ False)) → (p2 → p1)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218799701488196063594470461772 : ((p1 ∧ (True ∨ (p5 ∨ True))) → ((p2 ∧ ((p4 → p1) ∨ p4)) ∨ ((p2 ∨ (p4 → ((p3 → p3) ∧ p3))) ∨ (True ∧ ((p1 → p2) ∨ p1))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
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
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h7 =>
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
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52299302207952057514196699437 : (((((((p5 ∨ p2) ∨ p1) ∨ False) ∧ (p2 ∨ ((p5 ∧ p4) ∨ p4))) ∧ False) ∧ ((p4 → False) ∨ (p2 → ((True → (False ∧ True)) ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114826849278543202332407951417 : (((p2 ∨ (((False → p2) ∧ p3) → (((p5 ∨ (p4 ∧ p2)) ∨ True) → False))) ∧ (p5 ∨ ((p1 ∨ p3) ∨ (p5 ∧ (p2 ∧ False))))) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114023838776766766675570774253 : ((((p2 ∨ ((((False ∨ ((True ∧ True) ∨ p3)) ∨ (p3 ∨ p4)) ∨ (False ∧ (True ∧ p5))) ∧ p2)) ∨ p2) ∨ ((True → False) → p5)) ∨ (p3 ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684522995756406257265325249599 : (((((((False → p5) ∨ p5) → (p5 → p2)) → ((p2 ∧ (True → (p4 ∧ (p2 → p4)))) → p5)) ∨ (((p3 ∧ p5) → p1) → (p5 → True))) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_50930826059262923358222375416 : (((((((True ∨ p5) ∨ ((p5 ∧ p1) ∧ p3)) → (False ∧ p2)) → p2) → (p5 ∨ (p2 ∧ p3))) ∧ ((p5 ∨ p2) ∧ ((p3 ∧ p1) ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244647958777691443758719231551 : ((False ∧ p5) ∨ ((False ∨ p4) ∨ (((p5 ∧ p4) ∨ p1) → ((p1 → p2) → (((p3 ∧ p1) ∨ (p4 → True)) ∧ (False → (p2 ∧ (p2 ∧ p2)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- True on the right can always be proven directly.
    apply True.intro
  -- Implications on the right can always be decomposed.
  intro h9
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h9
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h9
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351638836808423322366923024580 : (p4 → ((((p5 ∨ (p2 → (False → p3))) → p4) → (((p4 ∧ p1) ∨ p5) ∨ (p1 ∨ p2))) ∨ ((False ∧ ((p1 ∧ (True → p3)) ∨ p3)) → p3))) := by
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
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346308735622437790397065613159 : (p3 → ((((p3 ∨ (p4 ∧ p2)) ∨ ((p1 ∨ p2) ∨ ((((p3 ∨ p4) ∧ p2) → p2) ∨ (((p5 ∨ True) ∧ True) → False)))) → p1) ∨ (p3 → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117778048177819057376162319071 : ((p4 ∧ ((((True ∨ True) → ((((p4 → p3) ∨ (True ∨ (p2 ∧ True))) ∧ (p3 ∨ p4)) ∨ p1)) ∧ p4) ∨ ((p5 → True) ∨ p1))) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150937418488539215521394932877 : (((True ∧ (p1 → (p2 ∨ (((((((False ∧ p1) ∧ p5) → True) ∧ p2) → p4) ∧ p4) → (True ∧ p4))))) ∨ p4) → (p2 ∨ (p4 ∨ (False → False)))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40158516530413454525900817458 : (((((((p2 → p3) → (p5 ∨ (p4 ∧ (False ∧ p1)))) ∧ p5) ∨ (True ∨ ((False ∧ True) ∧ ((True ∧ False) → (False ∨ p2))))) ∧ p1) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230785749316645515161807310482 : (((True ∧ p4) ∨ True) → (p4 → ((p1 ∨ (p1 ∨ True)) ∧ (((p1 ∧ p1) ∨ (p3 ∨ p5)) → (((p4 ∧ (p1 ∧ (p5 ∧ p1))) ∧ p5) ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Implications on the right can always be decomposed.
  intro h7
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h19
      case inr h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
    case inr h21 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h22 =>
        -- Conjunctions on the left can always be decomposed.
        let h23 := h22.left
        let h24 := h22.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h24
      case inr h25 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_751859826587358674716119551942 : (((True ∧ (p1 ∨ (False ∨ (p5 ∨ ((p2 → (p2 → ((p5 ∨ ((p1 → True) ∨ (((p4 ∧ (p3 ∨ p4)) ∨ p1) → p1))) → True))) → p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194063429962186032716397886306 : ((True → (((((p5 ∨ p3) ∨ p5) ∧ p4) ∨ p5) ∧ True)) → ((((p5 → p3) ∧ p3) ∨ True) ∨ (((True → True) ∧ p3) ∨ ((p2 ∧ p5) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51376156894693633818592044613 : (((((p2 → (p3 ∧ (p5 → (((True → ((p3 ∧ p1) ∨ p2)) ∧ p2) ∧ True)))) ∨ p4) ∨ p3) → ((p3 → (p2 → False)) ∨ (p5 ∨ True))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_312320123201400892722677159059 : (p2 ∨ (p2 → ((p3 ∧ (p5 ∧ p4)) ∨ (((((((p2 ∧ p1) → p4) → (p2 ∨ (p1 ∧ p2))) ∧ p5) ∨ p1) ∧ (p1 ∨ p2)) ∨ (False → p5))))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_155664284897550223533103084909 : (((p1 ∧ p2) ∨ (p2 ∨ (((p5 ∧ p3) ∧ ((p4 → p1) → p4)) → (((p2 ∨ p4) → p5) ∨ p5)))) ∧ ((p2 ∧ ((True → True) → False)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  let h4 := h2.left
  let h5 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40955777889274398462750011131 : (((((p1 → ((p4 ∧ ((((p2 → p3) ∧ (p5 → p2)) ∧ (False ∨ p2)) ∨ p5)) ∧ False)) ∨ (False ∧ (p2 ∧ p5))) ∨ (True ∨ p3)) ∨ p1) ∨ p4) := by
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
theorem thm_5_vars_51059029081242830854749354425 : (((p5 ∨ (p2 → (p2 ∧ ((((p1 ∨ (True ∧ ((p3 → p3) ∧ p5))) ∧ p1) ∨ p3) ∨ True)))) ∧ ((False → p1) ∧ (True ∧ (p5 → p5)))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121873312804832732372572658387 : (((True ∧ ((p4 ∧ (((True ∧ (True → (p4 ∧ (True ∨ ((False → p5) → (p5 ∨ p2)))))) ∧ p2) ∧ (p2 ∨ p4))) ∨ True)) → False) → (p5 → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (True ∧ ((p4 ∧ (((True ∧ (True → (p4 ∧ (True ∨ ((False → p5) → (p5 ∨ p2)))))) ∧ p2) ∧ (p2 ∨ p4))) ∨ True)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244831256729042317388701626256 : ((p1 ∧ p1) ∨ ((p1 ∧ p3) → (((p5 → p2) ∧ ((True → ((((p1 → False) ∨ (p5 ∧ p3)) ∧ True) → p1)) ∧ ((p5 ∨ p5) ∨ False))) ∨ p3))) := by
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
theorem thm_5_vars_67778992026952651146140289727 : ((p2 → ((False ∨ (((p1 ∧ p1) ∨ (p5 → ((p3 ∧ False) ∧ p4))) ∨ (p2 ∧ ((p5 ∨ p5) ∨ (True → ((p1 ∧ p3) → p3)))))) ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233026613452802009946150044452 : ((p4 ∧ (p3 ∧ p3)) → (((((p2 ∧ True) ∨ p1) ∨ p1) ∧ p2) ∨ (p2 ∨ ((p5 ∨ p2) ∨ (((p3 ∨ ((p5 ∨ p5) ∧ p1)) → False) ∨ p4))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



