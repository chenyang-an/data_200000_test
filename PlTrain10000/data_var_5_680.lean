variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_807380656502866328718318860706 : (((p4 → ((((p3 ∨ (p2 ∨ False)) ∨ p2) ∧ (p1 ∨ (p5 ∧ p2))) ∨ (((p4 ∧ False) → p3) ∧ (p5 ∨ (False → (True → (p1 → p4))))))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185745948088356401113474721793 : ((p3 → ((p3 → p3) → (((p1 ∨ p4) ∧ (p2 → True)) ∨ False))) ∨ (False → ((False ∧ (True → (p4 → ((p2 → (p3 ∧ p3)) ∧ p5)))) ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62622733569904538187879939721 : ((p4 ∧ (((((((False → False) ∧ True) ∨ (p1 → (p1 ∨ (p5 ∨ p2)))) ∧ p1) ∧ p1) ∧ ((p3 → (p4 ∨ (True ∨ p5))) ∨ p1)) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350353558490043776349577223489 : (p4 → ((p4 → (p5 ∨ (((((p4 → True) ∧ p2) ∨ p1) ∨ True) ∧ ((p1 ∨ (True → ((p4 ∨ p1) → (True ∧ (p4 → p5))))) ∧ p5)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_685638693236734027583801931146 : (((((((True ∨ p3) ∨ ((p5 → p1) ∧ (p4 ∨ (False ∨ False)))) → (p4 ∧ (p2 → p3))) ∨ True) → (True ∧ (p3 ∨ (p1 ∨ (p4 ∨ p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166658871561290636075012363621 : ((p1 → (p5 ∧ (((p3 ∧ (p3 ∨ p1)) ∨ p3) ∨ (p5 → ((p3 → (p1 → p2)) → p1))))) ∨ ((p4 ∨ p4) ∨ (True ∨ ((p2 ∨ False) ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354889893085710227310988372877 : (p5 → ((p3 ∧ ((p1 → (((p5 ∨ ((p2 ∧ p3) ∧ False)) → p4) ∧ (p3 ∨ False))) ∨ (False ∧ ((True ∨ p1) → (p5 → (False ∧ p5)))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217561805350693799826016647513 : ((((p4 ∧ p1) ∨ False) → False) → (p2 → ((False ∧ (((p3 ∨ (p1 → p1)) ∧ p5) ∧ ((p4 → False) ∧ p2))) ∨ (p4 → ((p5 → p5) ∧ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h4
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172445921312281496070855530957 : (((((True ∨ p3) ∧ p3) → p5) ∨ ((False ∧ False) ∨ (True → (True ∧ (p2 ∨ False))))) ∨ (((p3 ∧ p1) ∨ (p3 → (p1 ∨ (p3 → p3)))) ∨ p5)) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679403374352854736570543511205 : ((((p5 → ((((((p3 → p1) → p5) ∨ p5) ∧ (p2 → (((p1 ∨ p3) → p2) ∨ p2))) → p4) ∧ p3)) ∨ ((True ∨ p5) ∨ (False ∧ p1))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58049647233519508276127343660 : (((False ∧ False) ∧ (p4 ∧ (((p3 ∧ True) ∧ p4) ∨ ((p2 ∧ ((p5 ∧ p1) ∧ (False ∨ p3))) ∨ (p3 ∨ ((p5 → False) → (p2 ∧ p1))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55801489075542119183953376320 : ((((p2 → p4) ∨ (True → p4)) ∧ (False ∨ ((False ∨ (False ∧ ((True ∧ p3) → p1))) ∨ (((((p4 ∧ p4) ∨ p2) → p2) → p3) ∨ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345103055677666742606119175948 : (p3 → (((((p4 → True) → (p1 ∨ (p5 ∨ p5))) ∧ (p5 ∧ p5)) ∨ ((((p4 ∧ ((p4 ∧ p3) ∧ p3)) → True) ∧ (p4 → p2)) → True)) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51992253859437244570926750649 : ((((p3 ∨ p1) → (p2 ∨ (p3 → ((p1 → p5) ∨ (((True ∧ p3) ∨ p3) → p2))))) ∨ ((p2 → p1) ∨ (p2 → (p3 → (True ∧ True))))) ∨ p5) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_739483669588273474313192868754 : ((((p5 ∧ p1) ∨ ((((p1 → ((p2 → (p1 ∧ False)) → ((p4 → (p4 ∨ ((p5 → False) ∨ p2))) ∧ (p4 ∧ True)))) ∧ p3) → p2) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_599389471020231876468667821918 : (((((p4 ∧ p2) ∨ (((p3 → p1) ∨ (((p3 ∧ False) ∨ ((p1 → True) → True)) ∧ (p5 → (((p1 ∧ p4) → p3) ∧ p3)))) → p5)) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301053722113961889620610519218 : (False ∨ ((((p2 ∧ p1) → ((p4 ∨ p3) ∨ True)) → (p4 ∨ p2)) ∨ (p2 → ((p2 ∨ (((False → True) ∨ p4) ∨ ((p4 ∨ True) ∨ False))) ∨ p5)))) := by
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
theorem thm_5_vars_133973450528954964035429764723 : ((((((((p1 ∨ True) ∧ ((p3 ∨ (False → p1)) ∧ p2)) → ((p4 ∧ (p4 → True)) ∧ True)) ∨ p5) ∧ p5) ∧ p2) ∨ p5) ∨ (True ∧ (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319916953552668946850149673913 : (p4 ∨ (((p3 ∨ p2) ∧ (p3 ∨ p2)) → ((p5 ∧ p2) → ((p4 ∧ ((p5 ∧ p4) ∧ (((p1 → p3) ∨ True) ∧ ((p5 ∨ p1) ∧ p4)))) ∨ p5)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177981253130154168939665250566 : (((p2 ∧ (((p4 ∧ p2) ∨ (p1 ∧ (p5 ∧ True))) ∨ (p3 ∨ p1))) ∨ True) ∨ ((p3 ∧ (False ∧ ((p3 → False) → (p4 ∨ (p1 ∨ p1))))) ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177745113160218986008122228148 : ((((p1 ∨ (False → p2)) → ((True → (p3 ∧ (p4 ∨ p1))) ∨ p2)) ∧ p1) ∨ (True ∨ (((True ∨ p4) ∨ p5) ∧ ((p3 ∨ (p5 ∧ True)) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57089455219317371895541147854 : ((((p3 ∧ True) ∧ p3) ∨ (p2 ∧ (((p1 ∨ ((p3 ∨ p5) → p1)) → (True → (((p4 → True) ∧ p1) ∨ p5))) ∨ (p1 ∨ (p2 → p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256589836725869966404098285710 : ((p1 ∨ True) → (((p5 ∧ p1) ∨ (False ∨ ((p4 → ((((((p2 ∧ (p1 → True)) ∧ p5) ∧ p4) ∨ p3) → p2) ∧ False)) ∧ p1))) ∨ (False → p3))) := by
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
theorem thm_5_vars_179559238903486773794505432360 : ((p2 → (((p3 ∨ ((True ∨ (p1 ∨ p3)) ∨ (p3 → p4))) → False) ∨ p2)) ∨ ((((False ∨ p5) ∨ (p1 → (p5 → (True ∧ True)))) ∧ p5) ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55936650717482060406797420441 : (((p2 → (p5 ∧ (p5 → p4))) ∧ (((p5 → p4) → p1) → ((True ∧ (((p3 ∧ ((p4 ∨ p3) ∧ p5)) ∨ False) ∧ (True ∨ p4))) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111167644603800853924329863312 : ((((p5 ∧ ((p1 ∨ p1) ∨ p2)) ∧ (((p2 ∨ ((p2 ∨ p3) ∨ (p1 ∧ p3))) ∧ True) → ((p3 ∨ p1) ∧ (False ∧ p1)))) ∧ True) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246042172705094692567735858813 : ((p4 ∧ False) ∨ ((p4 ∧ (p3 ∧ p3)) → ((True → p5) → (p5 ∧ (p2 ∨ ((True → p3) → (p1 → (((False → (p4 ∧ p5)) → False) ∨ True)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h7 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h7
  -- One of the premise coincides with the conclusion.
  exact h8
  -- Conjunctions on the left can always be decomposed.
  let h9 := h1.left
  let h10 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h10.left
  let h12 := h10.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h13
  -- Implications on the right can always be decomposed.
  intro h14
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610459587246099427165509504296 : (((((((p3 ∨ False) → (((p2 ∧ (((p2 ∧ p1) ∨ p5) ∧ (False ∧ p2))) ∨ p3) ∧ ((p2 → p4) ∨ (p2 → True)))) → False) → p4) ∨ p4) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p3 ∨ False) → (((p2 ∧ (((p2 ∧ p1) ∨ p5) ∧ (False ∧ p2))) ∨ p3) ∧ ((p2 → p4) ∨ (p2 → True)))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- False on the left can always be used.
      apply False.elim h5
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- False on the left can always be used.
      apply False.elim h8
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h2
  -- False on the left can always be used.
  apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215114902670496170780578772961 : (((p2 → p4) → (p4 ∧ p5)) ∨ (p3 → (p2 ∨ ((p4 ∨ False) → ((p1 ∧ (((p5 → p2) ∨ ((p3 → p2) ∧ p5)) ∧ (True → p2))) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_769153032350829467972864486435 : (((p5 ∧ ((False → p3) ∧ (((p2 → True) ∨ ((p3 ∨ (p3 ∧ ((p4 → (p3 → ((p4 ∨ p1) ∨ p5))) ∧ p4))) → False)) → (p5 → p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149228291142755865755770453345 : (((p4 ∧ p1) ∨ ((p2 ∨ (p3 ∨ ((p3 ∨ (((p4 ∨ p1) ∧ p4) ∨ (p5 → p5))) ∨ False))) ∨ (p3 ∨ False))) ∨ (p4 → (p3 ∧ (p2 ∧ p2)))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703555231233710983075399762374 : ((((p2 → ((p2 ∧ (p4 ∧ ((p3 ∧ p1) → False))) ∨ p3)) ∨ ((p3 ∧ (False ∨ (p3 ∧ (((p3 → (False ∨ p4)) ∨ p3) ∨ p1)))) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65994199497159062755079717199 : ((p4 ∨ (p3 → (False ∨ (((p4 → False) ∧ ((p2 ∧ p3) ∧ ((p4 ∨ (p5 ∨ False)) ∨ (p2 → (p4 ∧ False))))) → (p4 → (True → p5)))))) ∨ p5) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h7.left
  let h10 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h13 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h12
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h14 := h5 h13
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- One of the premise coincides with the conclusion.
        exact h16
      case inr h17 =>
        -- False on the left can always be used.
        apply False.elim h17
  case inr h18 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h19 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h20 := h5 h19
    -- False on the left can always be used.
    apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613968668278103472423073130160 : (((((((p1 ∧ (False → ((True ∧ p4) ∧ (p3 ∨ p4)))) ∧ False) ∨ ((((p4 ∧ True) ∨ p2) ∧ True) ∨ p2)) ∨ (p1 ∨ (p3 → p4))) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_768665891981219918358657780747 : (((p5 ∧ (((((p3 ∨ ((p4 ∨ False) ∧ p4)) → p5) ∧ True) ∧ False) ∧ (((p2 ∧ p4) ∨ p4) ∧ ((False ∨ p1) ∧ (p5 ∨ (p2 ∧ p4)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216905420937132541073468608507 : (((p4 ∨ (p3 ∧ p2)) ∧ p2) → (True → ((p4 ∧ ((p2 ∨ True) → (p2 ∧ p1))) → ((((p4 → ((True ∧ False) ∨ p3)) ∨ p2) ∨ p1) ∧ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  -- Conjunctions on the left can always be decomposed.
  let h12 := h3.left
  let h13 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h1.left
  let h15 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h14
  case inl h16 =>
    -- One of the premise coincides with the conclusion.
    exact h16
  case inr h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713299834301760090049951834639 : ((((p5 ∨ (((p5 ∧ p5) ∧ p5) ∨ p4)) ∨ (((((((((p5 → p1) → p3) ∧ p5) ∨ p4) → p3) → True) ∨ False) → p1) → (p5 ∨ p1))) ∨ p5) ∧ True) := by
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((((p5 → p1) → p3) ∧ p5) ∨ p4) → p3) → True) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190859173604097199076767591238 : (((((p5 → (p3 ∧ p3)) ∨ p2) → p5) → (p5 → p1)) ∨ (((p5 ∧ ((p1 ∧ (p4 → p4)) ∨ p1)) ∨ (p4 → (p5 ∨ (p2 ∧ False)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780976784820013750874482123869 : (((p2 ∨ (((p5 → p4) → p2) → (p5 → ((p2 ∧ (((p3 ∧ (p4 ∨ p2)) → True) → p3)) ∧ ((False ∧ ((p5 ∧ False) ∧ True)) ∨ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55970873270995419558703157367 : (((((p2 → p5) ∨ False) ∧ False) ∨ (((True ∨ False) ∨ False) → (((p1 → p3) → ((p4 ∨ p5) → True)) → ((p1 ∧ True) ∨ (p3 ∨ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173101356819954925535848680218 : ((p1 ∨ (p5 ∨ ((True ∧ p5) ∨ ((((p3 → p5) → p3) ∨ True) ∨ (p3 → p1))))) ∨ ((((p5 ∧ (p3 ∧ p4)) ∧ p5) → (p3 → False)) → p2)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159221632070810625573554625391 : ((p2 → (p3 ∨ ((((True ∧ p1) → (p4 ∧ True)) ∨ False) → (((p1 ∧ (True ∨ False)) ∧ p4) ∧ True)))) ∨ ((p4 → (True ∨ p3)) ∨ (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181100869735443684890637858077 : (((p4 → p1) → ((p2 → (True ∨ p5)) ∨ ((p2 → (p4 ∨ True)) ∧ p1))) → (False ∨ (((p3 → (True → ((True ∨ p5) ∧ False))) ∨ p1) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_598503204529817137419545248117 : ((((((p5 → True) ∨ p3) → ((p1 → (p5 ∨ p2)) ∧ ((False ∧ ((p3 ∧ p2) → (((False ∨ p5) ∨ p3) ∧ p5))) ∨ (True → p1)))) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58773794212094675009598792644 : (((p4 → p3) ∧ (((True → (p1 ∧ p1)) ∧ p2) ∨ (True → (False ∧ ((p4 ∨ (((p5 ∨ p2) ∨ ((p4 → False) ∨ p2)) ∧ p4)) ∧ p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64124776579649459347325210377 : ((False ∨ (((False → p5) ∧ (p2 ∧ p5)) ∧ (p4 → (((p5 ∨ ((((p2 → False) ∨ True) ∧ p3) ∧ True)) → (p4 ∧ (p2 → False))) → p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198442538383393065184264448957 : ((p5 ∧ ((p2 ∨ ((False ∨ p4) ∨ p5)) ∧ p2)) ∨ (p5 → ((p2 ∧ (p1 → ((p2 → p1) ∨ ((p1 ∨ p5) ∧ False)))) ∨ (p4 → (p2 ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_487619018494856905905339531090 : (((((False ∨ (False → (p1 ∨ True))) → p1) → (p5 → ((False ∨ True) → (p1 ∧ ((p3 ∨ ((((p4 ∧ p1) ∨ False) ∨ p5) ∨ True)) ∧ True))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h6 : (False ∨ (False → (p1 ∨ True))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- False on the left can always be used.
      apply False.elim h7
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h8 := h1 h6
    -- One of the premise coincides with the conclusion.
    exact h8
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
theorem thm_5_vars_592964006895530154007861385046 : (((((p5 ∨ ((False ∨ ((p2 ∨ (((p5 ∨ ((p5 → False) → p2)) → True) → True)) ∧ (p4 → p1))) ∨ p5)) ∧ ((p5 ∨ True) ∨ p3)) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125377663045587558356578645297 : (((True ∧ True) ∧ (True → (((p5 ∧ ((p2 → p4) ∨ False)) ∧ ((p4 ∨ (p1 ∧ p2)) ∧ (p5 ∧ (p4 ∧ (False ∧ False))))) ∧ True))) → (True → p3)) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h7 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h8 := h4 h7
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- We need to get the right conjuct of h12 based on <expert-advice>.
  let h13 := h12.right
  -- We need to get the left conjuct of h13 based on <expert-advice>.
  let h14 := h13.left
  -- False on the left can always be used.
  apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712432790941321540481510653653 : (((((p2 ∨ (p3 ∨ p3)) ∧ (p1 → p5)) ∨ ((((p4 ∨ (((True → ((p4 ∨ p3) ∨ (p1 → p5))) ∨ True) ∨ False)) → p3) → p5) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601951516385199971548998237707 : ((((p4 ∧ (p4 ∨ ((p2 ∧ p2) ∧ (p4 ∧ ((p4 ∧ p5) → (p1 ∨ (p4 → ((p1 ∨ (p3 ∧ ((False ∧ p4) → p3))) ∧ False)))))))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225705209828271383989768073710 : (((p3 → p3) ∧ p3) ∨ (((False ∨ (p1 ∨ (((True → p4) ∨ (p5 ∨ (p5 ∧ (False → p4)))) ∧ p1))) ∨ True) ∨ ((False → (p2 ∨ p1)) ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219586050123836263428695516592 : ((True → (p2 ∧ (False ∧ False))) → ((False ∧ p1) ∨ (p1 ∧ (((p2 ∧ ((p1 → ((p5 → p5) → p2)) → p3)) ∨ True) → (p2 → (p4 ∧ True)))))) := by
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
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306440292268234602259878952009 : (p1 ∨ ((False ∨ p4) ∨ (p1 ∨ (p3 ∨ (((p2 → (p3 ∧ ((p5 ∧ ((p1 → (True ∨ p1)) → p5)) ∨ p3))) ∧ ((p1 ∧ p3) → p2)) → True))))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_760659605701462030968346604746 : (((p2 ∧ (p5 ∧ (((p5 ∨ p5) ∨ p2) ∧ (((p2 ∨ p5) ∧ ((p2 ∧ p1) ∧ (((p5 ∨ p4) ∨ (p4 ∨ p2)) → False))) ∧ (p3 ∨ p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225690149442645841517875190594 : (((p3 → False) ∧ p5) ∨ ((False ∧ p2) ∨ ((p1 ∨ (((p5 ∧ p2) ∧ (p5 → (True ∧ p5))) ∨ p1)) ∨ (False → (True ∨ (True ∧ (True ∧ False))))))) := by
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
theorem thm_5_vars_159166628113202524466031499244 : ((p1 → ((((((p4 → (p4 → p4)) ∧ p2) ∧ p5) → p3) ∨ (False ∨ p4)) ∨ (p2 → (p4 ∧ p5)))) ∨ (p5 → (((p5 → p1) → p2) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192993446704294450910027775035 : (((((p5 ∨ (p1 → p5)) → p1) ∨ True) → (False ∧ p2)) → ((((((False ∧ (True ∧ ((p4 ∨ p3) → p4))) ∨ p1) → p4) ∧ p1) ∧ p4) ∧ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4
  case inr h6 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h7 : (((p5 ∨ (p1 → p5)) → p1) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h8 := h1 h7
    -- We need to get the left conjuct of h8 based on <expert-advice>.
    let h9 := h8.left
    -- False on the left can always be used.
    apply False.elim h9
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h10 : (((p5 ∨ (p1 → p5)) → p1) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h11 := h1 h10
  -- We need to get the left conjuct of h11 based on <expert-advice>.
  let h12 := h11.left
  -- False on the left can always be used.
  apply False.elim h12
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h13 : (((p5 ∨ (p1 → p5)) → p1) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h14 := h1 h13
  -- We need to get the left conjuct of h14 based on <expert-advice>.
  let h15 := h14.left
  -- False on the left can always be used.
  apply False.elim h15
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h16 : (((p5 ∨ (p1 → p5)) → p1) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h17 := h1 h16
  -- We need to get the left conjuct of h17 based on <expert-advice>.
  let h18 := h17.left
  -- False on the left can always be used.
  apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707122805419944849206616967 : ((((p1 → p1) ∨ (p3 → ((False → (p4 → p5)) ∨ p1))) → (p3 ∨ (((p5 ∨ True) ∨ ((p5 ∧ p5) ∧ (False → p2))) ∨ p2))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136669823959453324914777224346 : (((p2 ∨ (p3 ∨ p3)) → (((p5 ∨ p1) ∨ (p5 → (False → (False ∧ False)))) ∧ (((p5 ∧ True) ∧ (p2 → p1)) → True))) ∨ (p5 ∨ (p5 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157678941307455025042817730414 : ((((False → True) → (p1 ∧ (((p3 ∧ p2) → p1) ∧ (p4 → (p2 → False))))) ∨ (False ∧ (p3 ∨ True))) ∨ (False ∨ ((p4 → p4) ∧ (p2 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247819722334177424468921884825 : ((p1 ∨ p1) ∨ (True → (((((((p4 ∧ False) → p4) → False) → (p2 ∨ (p4 ∧ (p4 ∧ (False ∧ p5))))) ∨ (p5 ∧ (p4 ∧ False))) ∨ True) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113435449009578402500179240652 : ((((((False ∧ (p4 ∨ (p2 ∧ p1))) ∨ ((p4 → ((p2 ∧ (p4 → p3)) ∧ p5)) ∨ p1)) ∧ (p4 ∨ p5)) ∨ False) ∨ (p3 ∧ p5)) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_734326513048767898951440219912 : ((((False ∨ p2) ∧ (p5 → (p1 → ((p1 → (((p4 → p4) → ((p5 ∨ p5) ∧ ((p1 ∧ p4) ∧ ((p1 ∨ True) ∧ p5)))) ∧ p2)) → p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611165206270427020380171561054 : ((((((True ∧ (p1 ∧ False)) ∨ (((((p3 ∧ p1) ∧ p2) → False) → (False ∨ ((p3 ∨ (p2 ∨ (p5 ∨ p2))) → p2))) ∨ p2)) → False) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305878538505931572556901129289 : (p1 ∨ (((True ∨ p1) ∧ (p1 → (p2 ∧ False))) ∨ ((p3 ∧ (p1 ∨ (False ∨ ((((p3 ∨ True) ∧ p2) → p2) ∧ p2)))) ∨ ((p2 ∧ p4) ∨ True)))) := by
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
theorem thm_5_vars_183891132752377166261298727922 : ((((p5 ∧ p3) ∧ ((p5 ∨ (p5 ∧ p4)) ∧ (True ∨ p2))) ∧ p1) ∨ ((True ∨ (p5 ∨ (((p2 → ((False ∨ p3) → p3)) ∧ p5) → p3))) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149630026067970512487953598538 : ((p4 ∧ (((((p3 ∧ ((p2 ∨ True) → p5)) ∧ (((p4 → False) ∧ p4) → (p5 ∧ True))) → False) ∨ False) ∨ p3)) ∨ (((p3 ∧ p1) → p1) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_734100712076789539244038387916 : ((((True ∨ p4) ∧ ((True ∨ ((((p5 ∨ p2) → True) ∨ ((((p2 ∧ (p1 → (True ∧ (p3 ∨ p3)))) ∧ p5) ∧ p2) → p1)) ∨ True)) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257004028500022878289265458392 : ((p2 ∨ True) → (((p4 ∨ ((p1 ∨ p5) → ((p4 → False) ∨ False))) ∨ (False → (p3 → (True ∧ (p4 ∧ (p4 → ((p3 ∨ p3) → p2))))))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h3
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h3
    case inr h8 =>
      -- False on the left can always be used.
      apply False.elim h3
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h10
    -- Implications on the right can always be decomposed.
    intro h12
    -- Implications on the right can always be decomposed.
    intro h13
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- False on the left can always be used.
      apply False.elim h10
    case inr h15 =>
      -- False on the left can always be used.
      apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135509924961252791860651951624 : (((False → (False ∧ ((p2 ∧ (p3 → (False ∧ (True ∨ ((p4 → p5) → (p3 ∧ False)))))) ∧ p5))) → ((False ∧ True) ∧ p5)) ∨ ((True → True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150252881022804712746012136191 : ((p3 → ((p1 ∧ ((p4 ∧ p2) ∨ ((((True ∨ False) → p2) ∨ False) ∨ p2))) ∨ ((p2 ∨ (p3 ∨ p1)) → True))) ∨ (True ∨ ((False → True) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197792241737280558140178512222 : ((((p4 ∨ p1) ∧ p2) ∨ (False ∧ (p4 ∨ p4))) ∨ (p5 ∨ (((False ∨ (p2 → True)) → (True ∧ (p3 → (p2 ∨ False)))) ∨ ((False ∨ False) → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_105089567588779409312125685754 : (((((p3 → (p5 ∧ ((((((p4 ∧ p4) ∨ (True ∨ p5)) ∧ p3) → True) ∧ p5) ∨ p2))) → p2) ∨ True) ∨ (p4 ∧ (p1 ∧ p2))) ∧ (p3 ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711584356321206935277305345842 : ((((p1 → (p5 ∨ (False → (p5 ∨ p3)))) ∧ (p5 → ((p1 ∨ ((False ∧ p3) ∨ p3)) ∧ (p4 → (((True ∧ (p5 → p1)) ∧ p3) → False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134181896999566729371636804849 : ((((p2 ∧ ((p1 ∧ ((p4 → (p5 ∧ p4)) ∨ (p1 ∧ p4))) ∨ p1)) ∧ ((True → p1) → ((p5 ∧ p4) ∧ False))) ∨ p3) ∨ (True ∨ (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117813007572204257370542270016 : ((p4 ∧ ((p2 ∧ False) ∨ (((p2 → ((p3 → p5) → (False ∧ True))) ∧ (p1 ∧ (p2 → ((True ∨ False) → p5)))) ∨ (True ∧ p1)))) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58258572183408009793034491935 : (((p5 ∧ p2) ∧ (p2 → (((True ∧ (p1 ∨ ((((p5 → ((p4 ∨ p1) ∧ ((p5 ∨ p4) → p2))) ∧ p3) ∨ False) → p5))) ∨ p3) → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_640086058402584992783297954619 : ((((((p1 ∨ True) ∧ True) → (p5 ∧ ((((p2 ∨ p5) ∧ (p2 ∧ True)) ∧ (p2 ∧ ((True ∧ ((p2 ∧ True) → False)) ∨ p5))) ∨ p5))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708276536102796791269469030561 : ((((p5 → (((p4 ∨ p1) ∨ p2) ∨ (p2 ∨ p1))) ∨ (p3 ∨ ((True ∨ (p3 → ((p3 → p3) ∧ False))) ∨ (p5 ∧ (p5 ∧ (p2 → p2)))))) ∨ p4) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197912265328627564886934223240 : (((False ∨ (p3 ∨ p3)) → ((p5 → False) → False)) ∨ ((p4 ∧ True) → (True → (((True → p1) ∨ (p3 ∨ (p5 ∧ False))) ∨ ((p4 ∧ False) → p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157074988133759082684800788493 : (((p1 ∨ (p4 → ((((p5 ∨ False) → (p5 ∧ (p5 ∨ (False → p1)))) ∧ p5) → (p3 ∨ False)))) ∨ True) ∨ (False → (p2 ∧ (True → (p1 ∧ p4))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137629470527222163742845242425 : ((False ∨ (((p2 → (p5 ∧ (p4 ∧ (p1 ∨ (p2 ∧ False))))) → ((p4 → (True → p4)) → (p3 ∨ p2))) ∧ (p3 ∧ p2))) ∨ ((p3 → True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690425314500747387873284522584 : ((((((p1 ∧ ((((p5 ∧ p1) ∨ ((p2 → p2) ∨ p5)) → p4) → False)) ∨ p5) ∧ p4) → (((p2 ∨ ((False ∨ False) ∨ p3)) ∨ p2) ∨ p5)) ∨ p4) ∧ True) := by
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
    let h5 := h4.left
    let h6 := h4.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : (((p5 ∧ p1) ∨ ((p2 → p2) ∨ p5)) → p4) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h14 =>
          -- One of the premise coincides with the conclusion.
          exact h3
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h15 := h6 h7
    -- False on the left can always be used.
    apply False.elim h15
  case inr h16 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h16
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315249475952585083949288551139 : (p3 ∨ (((p4 ∧ p5) ∨ (p5 ∨ p2)) ∨ (p3 → ((False → ((True ∧ ((p3 → p5) → (p4 → (p3 ∨ p3)))) ∧ p2)) ∨ ((p5 → True) ∧ p4))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66039242368344814851512561709 : ((p5 ∨ ((False ∨ (((p5 ∨ False) → p2) ∧ ((p4 ∧ (((p5 ∧ p2) ∧ p4) → (False ∨ ((p1 → (p3 → True)) ∧ False)))) ∨ True))) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117796375177161271591638365876 : ((p4 ∧ (((False ∨ (p1 ∧ ((p1 ∧ p4) ∨ True))) → p5) → (False ∨ (p2 ∧ ((True ∨ True) ∧ (((p4 ∨ True) ∨ True) ∧ p3)))))) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_784384011407143561480755511928 : (((p3 ∨ (p3 ∧ ((p5 ∧ (((p3 → (True ∨ True)) → p4) ∧ p5)) ∨ (((True ∧ (p5 ∨ p2)) ∨ (p2 → (False ∨ (p2 → False)))) → False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305158793251663256983578278997 : (p1 ∨ ((((((p1 ∨ (p3 ∧ p4)) ∨ ((p4 ∧ (True → p1)) ∨ True)) ∨ ((p5 ∨ p1) → p2)) ∨ p4) ∨ p4) ∨ (p3 → (False ∧ (p3 → p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314965433869375292027766838510 : (p3 ∨ ((p1 ∨ (p2 ∧ (((p1 → False) → (p2 ∨ p3)) ∧ p4))) → (False ∨ (p3 → ((((((p2 → False) ∧ False) ∨ True) ∨ False) ∧ True) ∨ False))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
theorem thm_5_vars_256144556681407929141500837601 : ((True ∨ p5) → (p5 → ((p2 ∧ (p2 ∧ (p4 ∧ ((((p3 ∨ p2) ∨ (p3 ∧ p5)) → (p2 ∧ (p2 → False))) → ((True ∧ p1) → p5))))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191463005602982618379613804691 : (((p5 → True) → ((p2 ∨ p4) → ((p3 ∨ p1) → p1))) ∨ ((((((p2 ∧ p4) ∧ (p3 → (p4 ∨ (False ∨ p1)))) → p4) ∧ p2) ∧ False) → p2)) := by
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
theorem thm_5_vars_655094317518275426848617262961 : (((((False ∨ (False → ((((p1 ∧ p1) → (p5 ∧ (p5 ∧ (True → (p3 ∧ ((True ∧ p1) → p3)))))) ∧ p2) → p2))) → False) ∨ (p1 → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150222749101837535628375865498 : ((p2 → (p4 ∧ (p5 ∧ ((True ∧ (False ∨ (False → (p1 → (p4 ∨ (True → False)))))) → (p5 → (p2 ∧ p1)))))) ∨ ((p2 ∨ p5) → (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209232563126807830794296985404 : ((p5 ∨ ((True ∨ (p2 ∧ False)) ∨ p3)) → ((p5 → (False ∨ ((((p1 ∨ True) ∨ p3) → (p3 ∧ (False → (p3 ∨ (p4 ∨ p4))))) → p1))) ∨ True)) := by
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
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- False on the left can always be used.
        apply False.elim h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209318609221065647998409645952 : ((False → (((p3 → p5) → True) ∧ p5)) → ((p2 ∧ (p4 → (p4 ∨ p3))) → ((((p4 ∧ p3) ∨ p4) ∨ p5) ∨ ((True ∨ False) → (True → True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54128362917893776551801194223 : (((p1 ∨ (p3 ∨ (p2 ∨ (p2 → ((p3 → p3) → p3))))) → ((p1 ∨ (((((p1 → p2) ∧ p1) ∨ (p5 ∨ p5)) → p1) ∧ p5)) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205667399210354174677822328287 : (((p1 ∨ p5) ∨ ((p2 ∧ p3) ∧ False)) ∨ (p4 ∨ (True ∨ (((True → (False ∨ (p3 → p5))) → (p1 ∨ p5)) → ((p4 → False) ∨ (p2 → False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158005844189452548125316580535 : (((p5 → ((((p1 → p3) ∨ p5) ∧ False) ∧ True)) → (p1 ∧ (((p1 ∨ True) ∧ p5) ∧ (p5 ∧ p2)))) ∨ (((p5 ∨ (p1 ∧ p2)) ∧ False) → False)) := by
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h3



