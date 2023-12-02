variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137216788696322483437406069323 : ((p1 ∧ ((((p3 → True) ∨ False) ∧ ((((p2 ∧ (True ∧ p5)) ∨ p5) → (p5 → False)) → (p4 ∧ (p4 ∨ p2)))) ∧ p1)) ∨ ((p4 ∨ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_85960717113823049930191232269 : ((((p2 → ((False → p5) → ((p5 → True) ∨ False))) → p5) ∧ (p1 → ((((p2 → p1) → True) ∧ (p3 → (p1 ∧ (p1 → p4)))) ∧ True))) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p2 → ((False → p5) → ((p5 → True) ∨ False))) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780654222137668461181853064979 : (((p2 ∨ (((((p5 ∨ (p5 → p5)) → True) ∧ p3) ∧ p4) ∨ (((p5 ∧ (((False ∨ p5) ∨ p1) → (p3 ∨ False))) ∧ p5) ∨ (True ∨ p1)))) ∨ p5) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178908614574891849836356945414 : (((p5 ∨ False) ∧ (((p4 ∧ (p5 ∨ p1)) → p5) ∧ ((p4 → p2) → True))) ∨ (False ∨ (((p5 ∨ (p4 → p4)) → (False ∨ False)) → (p2 → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (p5 ∨ (p4 → p4)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h3
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709148107285494628877559211393 : (((((p1 ∨ (p4 ∧ p2)) → ((p1 → p5) → True)) → ((((p3 ∧ p5) ∧ (p4 ∧ p1)) ∧ p5) → (((p4 → p1) → (p2 ∧ p1)) ∨ p1))) ∨ p1) ∧ True) := by
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
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h6.left
  let h10 := h6.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252290144732136854668174527104 : ((p4 → p5) ∨ ((False → (p2 ∨ ((False ∧ (True → (p5 → p5))) ∧ p1))) → ((p1 ∧ ((p3 ∨ p5) ∨ ((p3 ∧ p3) ∧ True))) ∨ (True ∨ True)))) := by
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
theorem thm_5_vars_113812258973674687974224646634 : (((p1 ∧ ((((((False ∧ p1) ∨ p3) → p2) → (p5 → p2)) → p1) ∨ ((((True ∨ p2) ∨ True) → p4) ∨ True))) → (p2 ∧ p2)) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_202591677866566721979244767293 : (((p4 → (p4 ∧ True)) ∨ (True → p4)) ∧ (((False ∧ p5) ∨ p2) ∨ ((p2 ∧ (((p5 → (p2 ∧ p3)) ∨ p2) → p4)) ∨ (p3 ∨ (p1 → True))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252413611858234691622608863506 : ((p5 → False) ∨ ((((p4 ∧ p3) → (False ∧ True)) ∨ False) ∨ (p1 ∨ ((p1 ∨ (p5 → p5)) ∧ ((False ∨ ((p5 → True) ∨ (p5 ∨ p5))) ∨ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265574086275360441100055857717 : (True ∧ (p1 ∨ ((((p3 → p5) → (((False → ((p2 ∨ p1) → (False → p5))) → p4) ∨ p2)) ∨ (p3 → (p1 → (False → (p1 → True))))) ∨ p1))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_782242884760680543794827918321 : (((p3 ∨ (((p5 ∧ p4) ∨ ((p1 ∧ ((p3 ∨ (((((p5 ∨ p5) → True) → p4) ∨ (True ∨ False)) → True)) → (True ∨ p3))) ∨ False)) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345394544174834061771027009227 : (p3 → (((((((p5 → False) ∧ p2) → (p2 ∨ ((p1 → ((p4 → p1) ∧ True)) ∨ ((p1 ∨ (p5 → p5)) ∨ p2)))) ∨ p4) ∨ True) → p4) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711825532586192709221151108774 : ((((((False → p1) ∨ (p5 ∧ p3)) ∧ p3) ∨ (((p5 ∨ (p3 → False)) ∨ p1) ∧ (((p3 ∧ p3) ∨ p1) ∧ ((p3 ∧ (True → p5)) ∧ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64612464330197707608662491154 : ((p1 ∨ ((p5 → True) → ((((((((False ∨ p2) ∧ (p2 ∧ (True → (False → p4)))) → p1) ∨ p3) ∨ p5) ∨ (True ∨ p4)) ∨ False) ∨ p4))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114395112695737368850869932376 : (((((p4 → True) ∨ (p3 → ((p5 ∧ (p3 ∨ (p3 ∧ p2))) ∨ p4))) → ((p5 ∨ p1) ∨ p5)) ∨ (p5 → (p1 ∨ (p4 ∧ p3)))) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111746214070528512314581140011 : ((((p5 ∨ (((p2 → p3) ∨ p1) ∨ ((True → p4) ∨ ((True → (p3 → ((p2 ∧ p5) → p2))) → (p3 ∧ False))))) → p2) ∨ p4) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337671008637439034710521700598 : (p1 → (((p5 ∨ p3) ∨ ((False ∧ (p3 ∧ ((False → p5) → ((p1 ∨ p2) → (p3 ∧ p5))))) ∧ p5)) ∨ (p5 → (p1 ∧ ((p1 → p1) ∨ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699704154303101374456943344697 : (((((p4 → ((p5 ∧ True) ∧ ((True ∧ (False → p5)) → False))) → p3) → (((p2 ∨ ((p1 ∨ False) ∧ p5)) ∨ (p5 → p5)) ∨ (p1 ∧ p5))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337057767998885090955187484424 : (p1 → ((((p2 ∨ (p3 ∧ (((True ∧ p1) → (((p3 ∧ p3) ∧ p1) → ((p4 → p4) ∧ False))) ∧ (p4 → p4)))) ∨ p5) → False) ∨ (True ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654532800966682720833427402068 : (((((p4 ∧ (p3 → ((False ∨ (p4 ∨ (p2 ∧ p1))) ∧ ((((False ∧ (p3 ∧ p5)) ∧ (p1 → p5)) → p1) ∨ p4)))) ∨ p5) ∨ (p2 → True)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_611543689549749990668546670808 : (((((True ∨ ((p2 → ((p5 ∧ True) ∨ (p1 ∨ ((p1 → p2) ∨ (((p1 → (p4 → p5)) → p1) ∧ (p5 ∧ p5)))))) ∧ p5)) → p2) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328412075709765213948264635269 : (True → (((((p2 ∨ p4) ∧ (p2 ∨ (p5 ∨ (p4 → (p5 ∧ p3))))) → (p4 ∧ True)) ∨ (False ∨ True)) ∨ (p4 → ((p4 → p1) → (True ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44611251019717621094335982971 : ((((p1 ∨ (p5 → (True ∧ (False → (p4 ∧ p5))))) → ((p2 → (p5 ∧ True)) ∨ (p5 → ((True → p1) ∨ ((p4 ∧ p3) ∧ True))))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299424690190403142562752710841 : (False ∨ ((p5 ∧ (((p1 → (False ∨ False)) → ((p2 ∨ False) ∨ (True ∧ p4))) ∨ ((p4 → (False ∧ (True ∨ ((p1 ∧ p4) ∨ p3)))) ∨ p5))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54140786102298393190403670302 : (((p5 ∨ (p4 ∧ (True ∨ (True → ((p1 → True) ∨ False))))) → ((p2 ∨ (((((p5 ∧ False) ∧ False) ∧ True) ∨ p5) → (p4 ∨ p4))) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_687037709392149004461437582500 : ((((p5 ∨ (p4 ∨ ((p1 ∨ (((p4 → p2) ∧ p5) ∨ (p5 → True))) ∧ (p4 → (False → p1))))) → (((p1 ∨ p3) ∧ p1) ∧ (p1 → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198259029848224208756767029155 : ((False ∧ (((p5 ∧ p1) → (p3 ∧ p5)) ∨ p1)) ∨ (((p1 ∨ True) ∧ p3) → ((True → True) → ((p2 ∧ (p4 ∨ ((False ∧ p2) → p5))) ∨ True)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_741593531656819784473482843857 : ((((p5 ∨ p5) ∨ ((p4 ∧ (p1 ∧ p1)) ∨ (((p5 ∧ ((((p3 ∧ p3) ∨ (p1 ∧ True)) ∨ p1) ∨ False)) ∧ ((p3 → p2) ∧ True)) → p5))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Conjunctions on the left can always be decomposed.
        let h11 := h3.left
        let h12 := h3.right
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- Conjunctions on the left can always be decomposed.
        let h16 := h3.left
        let h17 := h3.right
        -- One of the premise coincides with the conclusion.
        exact h4
    case inr h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h3.left
      let h20 := h3.right
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h21 =>
    -- False on the left can always be used.
    apply False.elim h21
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171656477470221377730956125269 : (((p1 ∧ ((((p3 ∧ (p5 ∨ (False ∨ False))) → p4) → p1) → (p1 ∨ p4))) ∨ p2) ∨ ((p4 ∨ (False ∨ False)) ∨ (True ∨ ((p3 ∧ False) → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40964270354426555522673729303 : (((((((p3 → p4) → (p4 ∧ p5)) ∨ (p3 ∨ p2)) ∧ (p4 ∧ ((p3 ∨ ((p3 → (p4 → p4)) ∧ p3)) ∧ p1))) ∨ (p1 → True)) ∨ p2) ∨ False) := by
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
theorem thm_5_vars_601060766104331541227554155520 : ((((p1 ∧ ((p3 ∨ p4) ∧ (p2 ∧ (p2 → (p2 ∨ (p4 → ((((False → (p2 ∧ p1)) → True) ∧ (p3 ∨ p2)) ∧ (p2 ∨ True)))))))) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774813251132738522429169446155 : (((False ∨ (((p2 ∨ True) → (p2 → (p4 ∧ p4))) → (((True ∨ (((p4 → p5) ∨ False) ∨ (False → (p3 ∧ p2)))) ∧ p5) ∨ (False → p1)))) ∨ p3) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350093803181089735078080886937 : (p4 → ((((((False ∨ False) ∧ (False ∧ ((p3 → (False ∨ ((p5 ∧ p3) ∨ False))) ∨ p4))) ∧ p4) ∧ (p1 ∨ p1)) ∨ (p4 → (False ∨ True))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54869669920401395282666366987 : ((((p1 ∨ ((p2 → False) ∨ p1)) ∧ p3) ∧ (((True ∨ True) → (p3 → ((False ∧ p5) ∧ (((False ∨ (p1 → False)) → p3) → False)))) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49319324491297250701194937075 : (((p3 ∨ (((False ∧ ((p1 ∧ p3) ∧ (p2 ∧ p2))) ∧ (p2 ∨ p3)) ∧ (False ∧ (p3 ∧ ((p5 ∧ p5) → True))))) ∨ (p5 ∨ (False ∨ True))) ∨ False) := by
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
theorem thm_5_vars_42874149893616142898407692654 : (((p2 → (p3 ∨ (((True ∧ ((((((p1 → True) → (p2 → p3)) → (p5 → p5)) ∨ p1) ∨ (p3 ∧ p3)) → p3)) ∧ p1) ∨ p2))) ∨ p2) ∨ p5) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248759438642191039965998730138 : ((p3 ∨ p3) ∨ ((p1 ∨ (((p5 ∨ p4) ∨ ((True → p5) ∨ (True → (p3 → True)))) ∨ (((p5 ∨ p3) ∨ p4) ∧ p3))) ∨ ((p3 ∧ p5) ∧ p3))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638004283112555906777519717372 : ((((((p1 ∧ (p3 → (True ∧ (p1 → False)))) → True) ∨ (((((p2 ∧ p2) → p2) → p5) → p5) → (p3 → (False ∨ (p2 ∧ True))))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_189927481577954925270105261978 : ((p3 → ((p1 ∧ p1) ∨ ((p3 ∧ (True ∨ p1)) ∧ True))) ∧ (((p5 ∧ (True ∧ p5)) ∨ False) ∨ ((p2 → True) ∨ (p2 → ((p3 ∨ True) ∧ p5))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229958614452608567227549431472 : (((True ∧ p4) ∧ True) → (((p4 ∨ (p3 ∨ ((((False ∨ (p1 → False)) ∨ ((p3 ∨ (True ∧ p5)) ∨ p2)) ∨ p5) → p3))) → p5) ∨ (p1 ∨ True))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680836617345087653346939690858 : (((((True → (p5 ∧ False)) ∨ (((p3 → p1) ∧ (p3 ∨ p3)) ∧ ((p5 ∧ p4) ∧ ((False → True) ∧ p3)))) → ((p1 ∨ (p2 → p2)) ∧ p3)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h4 := h2 h3
    -- We need to get the right conjuct of h4 based on <expert-advice>.
    let h5 := h4.right
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h8.left
      let h13 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h14 := h12.left
      let h15 := h12.right
      -- Conjunctions on the left can always be decomposed.
      let h16 := h13.left
      let h17 := h13.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h18
      -- One of the premise coincides with the conclusion.
      exact h18
    case inr h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h8.left
      let h21 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h22 := h20.left
      let h23 := h20.right
      -- Conjunctions on the left can always be decomposed.
      let h24 := h21.left
      let h25 := h21.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h26
      -- One of the premise coincides with the conclusion.
      exact h26
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h27 =>
    -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
    have h28 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h27, we can now drive its conclusion.
    let h29 := h27 h28
    -- We need to get the right conjuct of h29 based on <expert-advice>.
    let h30 := h29.right
    -- False on the left can always be used.
    apply False.elim h30
  case inr h31 =>
    -- Conjunctions on the left can always be decomposed.
    let h32 := h31.left
    let h33 := h31.right
    -- Conjunctions on the left can always be decomposed.
    let h34 := h32.left
    let h35 := h32.right
    -- Disjunctions on the left can always be decomposed.
    cases h35
    case inl h36 =>
      -- Conjunctions on the left can always be decomposed.
      let h37 := h33.left
      let h38 := h33.right
      -- Conjunctions on the left can always be decomposed.
      let h39 := h37.left
      let h40 := h37.right
      -- Conjunctions on the left can always be decomposed.
      let h41 := h38.left
      let h42 := h38.right
      -- One of the premise coincides with the conclusion.
      exact h42
    case inr h43 =>
      -- Conjunctions on the left can always be decomposed.
      let h44 := h33.left
      let h45 := h33.right
      -- Conjunctions on the left can always be decomposed.
      let h46 := h44.left
      let h47 := h44.right
      -- Conjunctions on the left can always be decomposed.
      let h48 := h45.left
      let h49 := h45.right
      -- One of the premise coincides with the conclusion.
      exact h49
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112002827782732795445363155455 : ((((p2 ∧ (p1 ∨ (p3 ∨ p5))) ∨ (((p1 ∨ True) ∧ p5) ∨ (p2 → ((((True → True) → (True ∧ p5)) ∧ p3) ∨ p1)))) ∨ p5) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656276917500485404954574804319 : ((((((p1 ∨ p4) ∨ (((p5 ∧ p5) ∧ p2) ∨ ((False ∨ True) ∧ p2))) ∧ ((p3 → p4) ∧ ((p2 ∨ p3) → (False ∧ p5)))) ∨ (True ∨ p3)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_201041175089522877485652821650 : ((p4 ∨ ((p3 ∨ True) → (False ∧ (p5 ∨ p1)))) → (((p1 ∨ ((p5 ∧ (True → p1)) ∨ ((True → p5) ∨ (p3 ∨ False)))) ∨ (True → p3)) ∨ True)) := by
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
theorem thm_5_vars_775654498551381549964531254468 : (((False ∨ (p1 ∨ (((True ∧ p4) ∨ (False ∨ (p1 ∧ p3))) ∨ (((p4 ∧ ((p3 ∨ (p2 ∨ ((p2 ∧ p5) ∨ p4))) ∨ p1)) ∧ False) ∧ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308510398783150912102331522050 : (p2 ∨ ((((((False → (False → (((p5 ∧ (p5 → p2)) → p5) → p2))) ∧ True) ∧ p2) ∧ True) ∧ (((p5 ∨ p4) ∨ (False → p1)) ∧ p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65893608746139136196814723447 : ((p4 ∨ (True ∧ (p1 → (p1 ∧ ((((p2 → (((p5 ∨ (p4 → p5)) → p4) ∧ (p3 → p5))) ∧ ((p2 ∨ p2) → p3)) → p2) ∨ True))))) ∨ p2) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52454500589499109144099481663 : (((p5 ∧ (((p5 ∧ ((p2 ∧ p5) → p4)) ∧ ((p2 ∨ False) ∨ False)) ∧ False)) ∧ ((p1 ∨ ((False → (p4 ∨ p3)) → False)) → (p1 → True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147103431061873066562206356275 : (((((p2 ∨ p1) ∨ p1) → (p5 ∨ ((((p2 → True) ∧ p3) ∨ p4) ∧ (((p2 ∨ p3) → True) ∨ False)))) ∧ p2) ∨ (((p1 → False) ∧ False) → False)) := by
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
theorem thm_5_vars_171621274837267372859234408512 : ((((p1 → (p1 ∨ p1)) ∧ (p2 ∨ (((p2 ∧ False) ∧ p2) ∧ (p5 → False)))) ∨ True) ∨ ((True ∨ (((p1 ∧ p4) → p5) → (p1 ∧ p1))) → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69111744487536650995564184443 : ((p5 → ((((((((p3 → p2) ∨ p2) ∨ p2) ∧ (p5 ∧ True)) ∧ p3) → (((p3 ∧ p1) ∨ p4) ∨ (p4 ∨ False))) ∧ p2) ∨ (p1 ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112524302005958893538100006506 : (((((p4 ∨ ((p3 ∧ ((p1 ∨ p5) ∧ ((p1 ∧ p1) ∨ p3))) ∧ ((((False ∧ p4) ∧ p2) → True) ∨ True))) → p4) → p2) → p5) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117005086863969023718185694619 : (((False ∨ p2) → (((((((True ∧ p3) → p5) → p1) ∨ (((((p1 ∨ p3) ∨ p2) ∧ False) ∨ False) ∧ p1)) ∧ p5) → p5) → p3)) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40867729556614901793820359148 : ((((((p5 ∨ p2) ∨ (((p3 → p1) → p3) → ((((p3 ∨ (p2 → p1)) → p2) → (p2 ∨ p3)) ∨ True))) → p4) ∧ (False ∧ p3)) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43589633211278004769760587207 : ((((((p4 ∧ (p3 ∧ p4)) ∧ ((p3 ∨ False) → ((((p3 ∨ False) ∧ (p1 ∧ (p2 ∨ p1))) ∧ (True ∧ p3)) ∨ True))) ∨ p4) → p5) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_398449050909612440811645372654 : ((((p5 ∨ (p2 ∨ ((((True ∨ False) → (p3 ∨ p1)) ∧ p2) → (True ∧ (((True ∨ p4) → ((True → p5) ∧ p5)) ∨ (p1 → p2)))))) ∨ p3) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61997262144072801056797111665 : ((p2 ∧ ((((p5 ∧ True) ∧ p4) ∧ True) ∧ ((p3 → p2) ∨ (False ∨ (False → (True ∧ (((((p3 → p2) ∧ p3) ∧ p3) ∧ p1) ∧ False))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232090716094675480638493697594 : (((p4 ∨ p5) → False) → ((((p1 ∨ ((p4 → p2) ∨ (True ∨ p2))) ∨ p1) → (p5 ∧ True)) → ((((True ∧ (True ∨ p4)) ∧ p3) → p4) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((p1 ∨ ((p4 → p2) ∨ (True ∨ p2))) ∨ p1) := by
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
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : (p4 ∨ p5) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h6
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146315448408732529524720746961 : ((False ∨ (((True ∨ (p2 → p4)) → ((p2 → (p1 ∨ False)) ∨ False)) ∨ ((p4 ∧ p1) → ((False ∧ False) → True)))) ∧ ((False ∧ p5) → (p4 → False))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173923929835129030506466617109 : ((((p4 → ((p2 → (False ∧ (True → p2))) → (False ∨ False))) ∧ (p4 ∨ True)) → p3) → (p3 → (((False ∨ False) ∨ (p3 ∨ p3)) ∨ (False ∧ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204154395617759188223578158600 : (((((p4 ∧ p3) ∨ p3) ∨ p4) ∧ p1) ∨ (True ∨ (p4 ∧ (((((True → p3) → p5) ∧ (p4 → (p2 ∨ p5))) ∨ ((True ∧ True) ∨ p1)) ∧ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148633049666802870540392376482 : (((p5 ∨ ((((p1 ∨ p4) ∨ p5) ∧ (p2 → p5)) ∨ p3)) → ((((False → p1) ∧ p3) ∧ p4) → (p4 ∧ p2))) ∨ ((False ∧ (p3 → p2)) → False)) := by
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
theorem thm_5_vars_60004165953138387870211336655 : (((False ∨ p5) → (((False ∨ (False ∨ (p4 ∧ (((True ∧ p4) ∧ p4) ∨ p3)))) ∨ (((False ∨ True) → p2) ∧ p3)) ∨ (p1 → (p1 ∨ True)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42723904719621157674647721732 : (((True → ((((((p1 → p3) ∧ False) → p2) ∧ True) → ((p4 ∨ ((p4 ∨ (False ∧ True)) ∨ p5)) → (p5 ∧ (False ∧ p4)))) ∧ p2)) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197502295491038084171273674244 : (((p1 ∨ ((p4 ∧ p5) ∨ False)) ∧ (p3 → p5)) ∨ ((False → ((False → (p1 ∧ ((False ∨ p2) ∧ p2))) → (p2 ∧ (p5 → False)))) ∨ (p3 ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50990454593630598424888813275 : ((((p3 ∨ p1) ∧ (p1 ∧ (p5 ∨ (True ∧ (p2 → ((p1 → p1) ∧ ((p4 ∨ True) → p1))))))) ∧ (((p4 → (p5 ∧ p1)) ∧ p3) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63301612895610859758984281461 : ((p5 ∧ ((True ∧ (p3 → p5)) → ((((p5 ∧ False) → (p5 → p5)) ∧ p4) → ((((False → ((p4 ∨ p5) ∨ p5)) ∨ True) ∨ p1) → p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677433957061970765762417117827 : ((((((((p1 ∨ p5) ∧ ((False ∧ False) ∨ ((p1 ∧ False) ∧ False))) ∨ (False → True)) ∨ (p5 ∨ p1)) ∨ True) ∨ (((p4 → False) ∧ p4) → p5)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_140299383674512340371923155982 : ((((p4 → False) ∧ ((p3 → (((((p4 ∨ True) → p3) ∨ p2) → (p4 → True)) ∨ p1)) → p4)) ∧ ((p4 → p5) ∧ p1)) → (False ∨ (p5 ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h3.left
  let h7 := h3.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h8 : (p3 → (((((p4 ∨ True) → p3) ∨ p2) → (p4 → True)) ∨ p1)) := by
    -- Implications on the right can always be decomposed.
    intro h9
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h10 := h5 h8
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h11 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h10
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h12 := h4 h11
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788138397272078934347902304767 : (((p5 ∨ (((((((True ∧ False) ∧ True) ∨ p3) ∨ ((p4 ∧ p2) ∨ p3)) ∧ p1) ∨ ((False → (True ∧ p4)) ∨ (p5 ∨ (p2 ∧ p2)))) ∧ True)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_625170405247915760072811804469 : ((((True → ((((p3 ∧ True) ∧ p5) ∨ (False → p2)) → ((((True ∧ p2) ∨ p2) → p1) ∧ (((True → (True ∧ p1)) → p1) ∧ p2)))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161621080629187171645597619320 : ((False ∨ (((p1 ∧ (False ∨ p4)) → p4) → (((p1 ∧ (True ∨ p1)) → (p2 ∨ p2)) ∧ (p4 ∧ p1)))) → (p2 ∨ (p4 → ((p4 → p5) ∨ p1)))) := by
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : ((p1 ∧ (False ∨ p4)) → p4) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- False on the left can always be used.
        apply False.elim h9
      case inr h10 =>
        -- One of the premise coincides with the conclusion.
        exact h10
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h11 := h3 h5
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- We need to get the right conjuct of h12 based on <expert-advice>.
    let h13 := h12.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187559557283862797902210704337 : ((p2 ∨ (p4 ∨ (True ∧ ((((p2 ∧ p1) ∧ p4) ∧ p5) ∨ p3)))) → ((True → (((((p3 ∨ False) → p2) ∨ p3) ∧ p3) ∨ p2)) ∨ (False → p2))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Conjunctions on the left can always be decomposed.
        let h13 := h11.left
        let h14 := h11.right
        -- Conjunctions on the left can always be decomposed.
        let h15 := h13.left
        let h16 := h13.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h17
        -- False on the left can always be used.
        apply False.elim h17
      case inr h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h19
        -- False on the left can always be used.
        apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56699893849783921646645100701 : ((((p2 ∧ True) ∨ p1) ∧ (p3 ∨ ((p2 → (p4 ∨ p4)) → (((p2 ∧ (p3 → (p3 ∨ False))) ∨ (p5 → p2)) ∧ (True ∧ (p1 → True)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61876854675994988247095115736 : ((p2 ∧ (((((p3 ∨ (p1 ∧ p4)) ∨ (p4 ∨ ((p5 → (False ∨ True)) ∧ (p5 ∨ (p4 ∨ p5))))) ∨ True) ∨ (p1 ∨ p1)) ∧ (p4 ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_899842379860074667189366443740 : (((((p1 ∧ (p2 ∨ ((p3 ∨ (p4 → False)) ∧ p4))) → (((p2 ∨ (False ∧ p4)) ∨ (p2 ∧ p4)) ∨ (p4 ∨ p4))) → ((p5 ∧ p2) ∨ False)) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p1 ∧ (p2 ∨ ((p3 ∨ (p4 → False)) ∧ p4))) → (((p2 ∨ (False ∧ p4)) ∨ (p2 ∧ p4)) ∨ (p4 ∨ p4))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h9
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h12 := h1 h2
  -- Disjunctions on the left can always be decomposed.
  cases h12
  case inl h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- One of the premise coincides with the conclusion.
    exact h14
  case inr h16 =>
    -- False on the left can always be used.
    apply False.elim h16
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310415807546169841479842933850 : (p2 ∨ (((p2 → ((True ∧ (p1 → p4)) ∨ p4)) ∧ p2) → (((((False ∨ p1) ∨ ((p3 ∨ (p4 ∧ p4)) ∨ p3)) ∨ p5) ∧ p4) → (p1 ∨ p4)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- False on the left can always be used.
        apply False.elim h7
      case inr h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h1.left
        let h10 := h1.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h8
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- Conjunctions on the left can always be decomposed.
          let h14 := h1.left
          let h15 := h1.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h4
        case inr h16 =>
          -- Conjunctions on the left can always be decomposed.
          let h17 := h16.left
          let h18 := h16.right
          -- Conjunctions on the left can always be decomposed.
          let h19 := h1.left
          let h20 := h1.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h4
      case inr h21 =>
        -- Conjunctions on the left can always be decomposed.
        let h22 := h1.left
        let h23 := h1.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
  case inr h24 =>
    -- Conjunctions on the left can always be decomposed.
    let h25 := h1.left
    let h26 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172344045373861213494794548138 : (((p2 ∨ (p3 ∨ (False ∧ (True → p2)))) ∧ ((p2 ∨ (p2 ∨ (p2 → p4))) ∧ p3)) ∨ ((((p1 ∧ p2) ∨ p5) → p5) → (True ∨ (p4 ∧ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115226309510874719413609294844 : (((((p4 ∨ p5) ∧ (True ∧ (True ∨ (True ∨ p5)))) ∧ True) ∨ (p5 ∨ (p2 ∧ (((False ∨ ((p4 ∨ p4) ∧ p3)) ∨ p5) ∧ p1)))) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264406997120049340215505907968 : (True ∧ ((p5 ∧ ((False ∨ False) → True)) ∨ ((p5 ∧ True) ∨ ((p1 ∨ ((p2 ∧ p5) ∨ (((p1 ∨ p3) ∨ False) ∨ (p1 → (True ∨ True))))) ∨ p4)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52277296876821215650908965739 : (((p2 → ((((((False → p5) ∧ p3) ∧ (p2 → p1)) → (p3 → p3)) ∨ p3) → p5)) → ((p5 → ((p2 → p2) → (p3 ∨ p4))) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172635815656220367655241624996 : (((p5 ∧ p4) ∧ ((p2 ∧ ((False → p5) ∧ p3)) ∨ ((p1 ∨ True) ∧ (p5 → p3)))) ∨ ((True → ((True ∧ False) ∧ p5)) → ((p5 ∨ p5) ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h6
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225913603689008335041223645698 : (((p1 ∧ p5) ∨ p3) ∨ (False ∨ (p4 ∨ (p4 ∨ (((p4 ∧ p4) ∧ (True ∨ ((False ∧ True) ∨ p5))) ∨ ((False → (p4 ∨ (p3 → p4))) ∨ p5)))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620868559196308038846110380549 : (((((p1 ∨ p3) → (p2 ∨ ((((p2 → (False ∧ ((True ∧ p5) → (p4 ∨ p3)))) ∧ p1) → p4) ∨ (p3 ∧ (p1 ∨ (True ∨ p1)))))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141333578679960982718354719163 : (((((p5 → p5) → p1) → p2) ∨ ((p1 ∧ (p2 → (((p2 ∨ (p3 ∧ p2)) ∧ (False ∧ p2)) → (p1 ∧ p4)))) → p4)) → ((True → False) → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56826044761981735674966340809 : ((((p1 → p1) → p4) ∧ (((p3 ∧ (False → (p4 ∧ (p2 → p3)))) ∨ ((p2 → p4) ∨ p1)) ∧ (p2 ∧ ((p3 ∨ p4) → (p3 → p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_786494533014414623614773588107 : (((p4 ∨ ((p4 ∧ ((((False ∧ p5) → (p3 ∧ p2)) → True) → (p3 → p4))) ∨ (p2 ∨ (p1 → (((p4 ∧ (p2 ∧ p1)) → p5) → p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_750019722618158540708858002648 : (((True ∧ (((False → ((p2 ∨ (True ∨ (p1 → p5))) → p2)) ∨ (((p4 → (p4 → (False → (p3 → p2)))) ∧ (p5 → p5)) ∧ p4)) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165529559637674043158264737706 : (((False ∨ ((False ∨ ((p2 ∨ p4) ∨ (p1 ∨ p5))) → p5)) → (((p1 ∧ p1) ∧ p1) → p4)) ∨ (p4 → ((False ∨ p5) ∨ (p3 → (p2 → p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158537027554119581419329790411 : (((p1 → p1) → (((p4 ∨ p5) → (p2 ∨ p3)) → (p3 → ((p1 ∨ p5) → ((False → True) → p4))))) ∨ ((p3 → (p1 → p4)) → (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721164985416806598174069497627 : (((((p4 → p2) ∨ (True → p2)) → (((p2 ∧ ((p3 → ((p2 ∨ (True ∧ p5)) ∨ True)) ∧ p5)) ∧ p5) ∨ (((p4 ∧ p5) → p2) → True))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115685922160156984838460044809 : (((p1 ∨ (p5 ∧ ((p5 ∨ p1) ∧ p3))) ∨ (False → ((p4 → (True ∧ (p2 ∨ (p2 → p5)))) ∧ (((True → p4) ∨ p4) → p1)))) ∨ (p4 ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h1
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323889116277799276028423261124 : (p5 ∨ ((((p1 ∨ False) ∧ ((False ∨ False) ∨ ((p3 ∧ p1) ∧ (p5 ∨ (False ∨ p4))))) ∨ p1) ∨ ((((False ∧ p3) → p1) ∨ (p2 ∨ False)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47514768607737460473347919946 : (((p2 ∨ (p3 ∨ ((p5 ∨ ((p5 ∧ p5) → p5)) ∧ (p1 → (p2 ∨ (((p2 ∧ p3) ∨ False) ∨ (p1 → (p4 ∧ p5)))))))) ∨ (p3 → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_723812448814537248001336061372 : (((((p3 → p5) → p5) ∧ (((p2 → ((p2 ∧ (p4 → p3)) → (p1 ∨ True))) ∨ (p5 ∨ p3)) ∧ (((p5 → (p1 ∧ p2)) ∧ False) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38036061783233603294723842632 : ((((((p2 ∨ ((p1 ∨ ((((p2 ∨ True) ∧ (p4 ∧ p2)) ∨ p1) ∨ p4)) ∨ (p5 ∧ (p5 ∧ p4)))) → True) ∨ True) → (p3 ∧ False)) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56468760928210497007033434962 : ((((p1 ∨ p2) → (p4 ∨ True)) → (((p3 → (p5 ∨ ((p5 ∨ False) → ((p2 → False) → p4)))) → (p1 → p4)) → (p5 → (p4 ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139929959696280256647312892157 : ((((((p5 ∨ True) ∧ p4) ∨ True) ∧ ((((p4 ∧ ((False ∧ p5) → True)) ∨ True) ∨ p5) ∧ (False → True))) ∧ (p3 ∨ False)) → (p3 ∧ (p2 ∨ True))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h5.left
      let h11 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- Conjunctions on the left can always be decomposed.
          let h14 := h13.left
          let h15 := h13.right
          -- Disjunctions on the left can always be decomposed.
          cases h3
          case inl h16 =>
            -- One of the premise coincides with the conclusion.
            exact h16
          case inr h17 =>
            -- False on the left can always be used.
            apply False.elim h17
        case inr h18 =>
          -- Disjunctions on the left can always be decomposed.
          cases h3
          case inl h19 =>
            -- One of the premise coincides with the conclusion.
            exact h19
          case inr h20 =>
            -- False on the left can always be used.
            apply False.elim h20
      case inr h21 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h22 =>
          -- One of the premise coincides with the conclusion.
          exact h22
        case inr h23 =>
          -- False on the left can always be used.
          apply False.elim h23
    case inr h24 =>
      -- Conjunctions on the left can always be decomposed.
      let h25 := h5.left
      let h26 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h25
      case inl h27 =>
        -- Disjunctions on the left can always be decomposed.
        cases h27
        case inl h28 =>
          -- Conjunctions on the left can always be decomposed.
          let h29 := h28.left
          let h30 := h28.right
          -- Disjunctions on the left can always be decomposed.
          cases h3
          case inl h31 =>
            -- One of the premise coincides with the conclusion.
            exact h31
          case inr h32 =>
            -- False on the left can always be used.
            apply False.elim h32
        case inr h33 =>
          -- Disjunctions on the left can always be decomposed.
          cases h3
          case inl h34 =>
            -- One of the premise coincides with the conclusion.
            exact h34
          case inr h35 =>
            -- False on the left can always be used.
            apply False.elim h35
      case inr h36 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h37 =>
          -- One of the premise coincides with the conclusion.
          exact h37
        case inr h38 =>
          -- False on the left can always be used.
          apply False.elim h38
  case inr h39 =>
    -- Conjunctions on the left can always be decomposed.
    let h40 := h5.left
    let h41 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h40
    case inl h42 =>
      -- Disjunctions on the left can always be decomposed.
      cases h42
      case inl h43 =>
        -- Conjunctions on the left can always be decomposed.
        let h44 := h43.left
        let h45 := h43.right
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h46 =>
          -- One of the premise coincides with the conclusion.
          exact h46
        case inr h47 =>
          -- False on the left can always be used.
          apply False.elim h47
      case inr h48 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h49 =>
          -- One of the premise coincides with the conclusion.
          exact h49
        case inr h50 =>
          -- False on the left can always be used.
          apply False.elim h50
    case inr h51 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h52 =>
        -- One of the premise coincides with the conclusion.
        exact h52
      case inr h53 =>
        -- False on the left can always be used.
        apply False.elim h53
  -- Conjunctions on the left can always be decomposed.
  let h54 := h1.left
  let h55 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h56 := h54.left
  let h57 := h54.right
  -- Disjunctions on the left can always be decomposed.
  cases h56
  case inl h58 =>
    -- Conjunctions on the left can always be decomposed.
    let h59 := h58.left
    let h60 := h58.right
    -- Disjunctions on the left can always be decomposed.
    cases h59
    case inl h61 =>
      -- Conjunctions on the left can always be decomposed.
      let h62 := h57.left
      let h63 := h57.right
      -- Disjunctions on the left can always be decomposed.
      cases h62
      case inl h64 =>
        -- Disjunctions on the left can always be decomposed.
        cases h64
        case inl h65 =>
          -- Conjunctions on the left can always be decomposed.
          let h66 := h65.left
          let h67 := h65.right
          -- Disjunctions on the left can always be decomposed.
          cases h55
          case inl h68 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h69 =>
            -- False on the left can always be used.
            apply False.elim h69
        case inr h70 =>
          -- Disjunctions on the left can always be decomposed.
          cases h55
          case inl h71 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h72 =>
            -- False on the left can always be used.
            apply False.elim h72
      case inr h73 =>
        -- Disjunctions on the left can always be decomposed.
        cases h55
        case inl h74 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h75 =>
          -- False on the left can always be used.
          apply False.elim h75
    case inr h76 =>
      -- Conjunctions on the left can always be decomposed.
      let h77 := h57.left
      let h78 := h57.right
      -- Disjunctions on the left can always be decomposed.
      cases h77
      case inl h79 =>
        -- Disjunctions on the left can always be decomposed.
        cases h79
        case inl h80 =>
          -- Conjunctions on the left can always be decomposed.
          let h81 := h80.left
          let h82 := h80.right
          -- Disjunctions on the left can always be decomposed.
          cases h55
          case inl h83 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h84 =>
            -- False on the left can always be used.
            apply False.elim h84
        case inr h85 =>
          -- Disjunctions on the left can always be decomposed.
          cases h55
          case inl h86 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h87 =>
            -- False on the left can always be used.
            apply False.elim h87
      case inr h88 =>
        -- Disjunctions on the left can always be decomposed.
        cases h55
        case inl h89 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h90 =>
          -- False on the left can always be used.
          apply False.elim h90
  case inr h91 =>
    -- Conjunctions on the left can always be decomposed.
    let h92 := h57.left
    let h93 := h57.right
    -- Disjunctions on the left can always be decomposed.
    cases h92
    case inl h94 =>
      -- Disjunctions on the left can always be decomposed.
      cases h94
      case inl h95 =>
        -- Conjunctions on the left can always be decomposed.
        let h96 := h95.left
        let h97 := h95.right
        -- Disjunctions on the left can always be decomposed.
        cases h55
        case inl h98 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h99 =>
          -- False on the left can always be used.
          apply False.elim h99
      case inr h100 =>
        -- Disjunctions on the left can always be decomposed.
        cases h55
        case inl h101 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h102 =>
          -- False on the left can always be used.
          apply False.elim h102
    case inr h103 =>
      -- Disjunctions on the left can always be decomposed.
      cases h55
      case inl h104 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h105 =>
        -- False on the left can always be used.
        apply False.elim h105



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118911779951494299998067459701 : ((True → (p4 → (((((p4 ∧ (p4 → p1)) ∨ (True ∨ (False → p3))) ∧ ((((p2 → p2) ∨ p5) ∧ p2) ∧ False)) → p1) → p2))) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_805520870892982566280615146154 : (((p3 → (p4 ∨ (((((p2 ∧ (p5 ∧ p1)) ∨ ((p4 ∨ p2) → (p1 ∨ ((p1 ∧ p1) ∨ p2)))) ∧ p1) ∨ (p4 → p1)) ∨ (False → p2)))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



