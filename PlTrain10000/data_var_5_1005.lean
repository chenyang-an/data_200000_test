variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350823135290686855950083745969 : (p4 → ((((p5 ∨ False) ∨ ((((True ∨ p4) ∨ (p2 → p2)) → ((p1 → (p1 → p4)) → p5)) → (False ∨ False))) ∨ (p3 → p4)) ∧ (p2 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53563995737003789632771121883 : (((((True ∧ (p5 ∨ (p3 ∧ p4))) ∧ (p1 ∧ False)) ∨ p1) ∧ (False → (p4 ∨ ((((p3 → p2) ∧ (p4 ∨ (p2 → p5))) ∨ p5) ∨ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166106342794437643914147273477 : (((p3 → p3) → (True → (False ∧ ((True ∨ False) → (False ∨ (p2 → (p5 ∧ (p3 ∨ False)))))))) ∨ ((True ∧ p1) → (p4 → ((p3 ∨ True) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198769454782278399958161933054 : ((True → (p3 ∨ (p2 ∧ ((p2 ∨ True) ∨ p2)))) ∨ ((((p2 ∧ p5) ∧ p1) → False) ∨ ((True ∨ (((p1 ∧ p4) ∧ (p4 → p4)) ∨ True)) ∨ p1))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165779413050711328228061449103 : ((((p1 ∨ p1) → (p3 ∨ p4)) → ((p4 ∨ True) ∧ (((p4 ∨ p1) → False) ∧ (p5 → p2)))) ∨ (((True ∧ (True → True)) ∧ (True ∧ False)) → p5)) := by
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
  let h6 := h3.left
  let h7 := h3.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159285317319027035084945743272 : ((p4 → ((False → (p5 → (p2 ∨ p3))) → ((p1 → False) ∨ ((p5 ∧ p3) → ((p2 → p4) → p3))))) ∨ ((p3 ∧ (p4 → p4)) ∧ (p4 → False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246348215213942215022960701359 : ((p4 ∧ p5) ∨ ((p5 ∧ p2) ∨ ((((((p4 ∧ (p3 → True)) → True) → (True → p4)) → (p1 ∧ (p2 → (False → p2)))) ∧ p2) ∨ (True ∨ p3)))) := by
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
theorem thm_5_vars_190023963434151337913764450731 : ((((p3 ∧ (p4 ∨ (p1 → (p2 → False)))) ∧ p5) ∧ p1) ∨ (((((p4 ∨ (p2 ∧ (p1 ∧ p4))) → (False → p5)) ∨ True) → (p3 ∨ p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207464125297913586911852708419 : (((True → (p4 ∨ (True ∧ p2))) ∨ p3) → (False ∨ ((p3 ∨ (p4 ∧ p2)) ∨ (p5 → ((((p2 ∧ (p3 → (p5 ∧ p2))) ∨ p5) → p5) ∧ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49954927701216264262807564804 : ((((((((((p2 ∨ True) ∧ (p5 ∨ (True ∧ True))) → p1) ∨ p3) → p5) ∧ p3) → p1) → (p3 ∧ p4)) ∧ (True → ((p1 ∨ p5) ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197720568921605087361639560414 : ((((p2 → p2) ∧ p4) ∧ (p4 → (p3 ∧ False))) ∨ ((((p4 ∨ (p1 ∨ (p5 ∨ p4))) ∧ (p5 ∧ (True → (p4 ∧ (p5 → False))))) ∨ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_86566553291269624746955917257 : (((((p4 → p2) → (False → (p3 ∧ True))) ∨ p3) ∧ (((p3 → p1) → True) ∧ (p2 ∧ (p5 → (((p3 ∨ (p5 → True)) → p1) → p2))))) → p2) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h3.left
    let h11 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150040002892587408902857046428 : ((p5 ∨ (p4 ∨ (((p5 ∨ p3) ∧ ((False ∧ True) ∧ ((p4 ∨ (p3 ∨ (p3 → p5))) ∨ p2))) ∧ (p1 → False)))) ∨ (((p2 ∧ p5) ∧ True) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205045303314312299205275135528 : (((True → (p5 → (p3 → p3))) → p3) ∨ ((((p5 ∧ True) ∨ ((((False ∨ p3) ∨ p5) → p3) ∨ (False → p3))) ∧ (True ∨ p5)) ∧ (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299125356791463718437975366712 : (False ∨ ((((((p1 → p2) → ((p4 ∨ (p1 ∧ (((False → p1) ∨ True) ∨ True))) ∧ (p3 ∧ (p4 ∨ p4)))) ∨ (True ∧ p5)) ∨ p5) ∨ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328403951685638568112484294444 : (True → (((((p1 ∨ (False ∧ p2)) ∧ ((((p4 ∧ p3) ∨ (p4 ∨ True)) ∨ False) ∧ p4)) ∨ p4) ∨ p2) ∨ (False → ((p5 ∧ p2) ∧ (p4 ∧ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316505606784743887307061937021 : (p3 ∨ (p2 ∨ ((p2 ∨ ((((p3 ∨ True) → (((p3 → (p3 ∧ False)) → p4) ∧ True)) ∧ (p5 ∨ p3)) ∧ p5)) ∨ (((p4 ∨ p1) → p3) → True)))) := by
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
theorem thm_5_vars_204806053370377235476717692766 : (((((p4 → p3) ∧ p2) ∨ False) → p4) ∨ (p1 ∨ (((p5 → (False ∨ p4)) ∨ False) → ((p1 ∨ ((False ∨ p2) → (p1 ∧ p3))) ∨ (False → True))))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49816539300444954972945742123 : (((p1 → (p3 → ((p1 ∧ ((p2 ∧ (p4 → p5)) ∨ p2)) → ((True ∨ p1) → (p5 ∨ (p5 ∧ (p4 → False))))))) → (p3 ∨ (p5 ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47214402349616344404822128801 : ((((False ∧ ((p5 ∧ (p2 → p4)) ∧ ((p4 ∨ p5) ∨ False))) ∨ (p1 → (p5 ∧ ((p2 ∧ p3) ∧ (p4 ∧ (p4 ∨ True)))))) ∨ (True → True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355579462788688789147650895025 : (p5 → (((p3 ∧ (((p4 → ((p3 → False) → (True ∧ p2))) → p3) ∧ (False ∨ True))) ∨ ((False ∨ (p5 → p3)) ∨ (True → False))) ∨ (p3 → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47576407565701624199378988032 : (((p1 → (((p1 → (((False ∨ p2) ∧ (p3 ∧ (p1 ∨ p4))) ∧ p5)) ∨ p5) → (True → ((p2 → (p3 ∧ p2)) ∧ False)))) ∨ (True ∨ p4)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60841168766875841106535159926 : ((True ∧ (p1 ∨ (((p2 ∧ p3) → p1) → (((True ∧ True) → True) → ((((p3 ∧ ((True → (True ∧ p1)) ∨ p3)) ∧ True) ∨ p3) ∨ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110915520842606887798480458865 : ((((p1 ∨ ((True ∧ p4) ∨ (((p1 → p4) ∨ (p2 ∨ p2)) ∨ ((p2 ∧ p5) → (((p4 ∧ False) ∨ p2) → False))))) → p1) ∧ p1) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149933326032267889440785180517 : ((p3 ∨ ((p4 → (p3 ∧ True)) ∧ ((((True ∨ p2) ∨ p5) → (True ∨ (p5 ∨ ((p1 → p5) → p3)))) → False))) ∨ ((p5 ∧ (p5 → False)) → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313267853863966948576368192104 : (p3 ∨ ((False ∧ (p4 ∨ ((((True → (p3 ∨ p2)) → False) ∨ (p5 ∨ ((p2 → p4) ∨ (((True ∨ p3) ∧ (p3 → p4)) ∧ p2)))) ∧ p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348831460880806522625125692590 : (p3 → (p1 ∨ (False ∨ ((p5 ∨ (False ∨ ((p3 → True) → ((False ∨ False) ∧ p5)))) ∨ ((p3 → ((p3 ∨ (p2 ∧ p4)) ∧ p3)) ∨ (p4 → p2)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712472234906017870093484682126 : ((((((p3 ∧ p3) ∨ p3) ∨ (p2 ∧ p1)) ∨ ((p1 ∨ (((p4 ∨ (p3 ∧ (p5 → p5))) ∨ False) ∧ (((p1 → p4) ∨ p2) ∧ False))) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338684942379856876267989547939 : (p1 → ((p1 ∨ True) ∧ (((p4 → p4) ∨ p5) ∧ (p1 → ((p3 ∧ (((True ∧ p5) ∨ (p4 ∨ ((True → p3) ∧ (p5 → p2)))) ∨ False)) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323780868225960070442575830874 : (p5 ∨ ((((((True → p3) ∨ ((True → True) → False)) ∧ ((False ∨ (True ∨ False)) ∨ p2)) ∨ p2) ∨ True) ∨ ((p5 → (p2 ∨ p5)) ∧ (p4 ∧ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38303837536939611248482460856 : (((((((((p2 ∨ p3) ∧ p2) ∧ p1) → ((((p3 → True) ∨ p3) ∧ p1) → p5)) → False) → False) → (((True ∨ False) → p2) → False)) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191951332088089951482380570735 : ((True → (p2 → (((p3 → p3) → p3) ∨ (False ∨ False)))) ∨ ((p4 ∧ p2) ∨ ((False → (p2 → (False → p4))) ∨ ((p1 ∧ (p2 → p4)) → p5)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354963387711689975442707383456 : (p5 → ((p2 → (((p4 ∨ p5) ∧ ((p4 ∧ p3) ∨ p1)) ∨ (((False ∨ False) ∨ ((((True ∧ (p4 ∨ True)) ∨ True) → True) ∨ True)) ∧ p2))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316742032205348716219146746734 : (p3 ∨ (True → ((((False ∨ ((p1 ∨ (False ∨ p5)) ∨ (((False → (p4 ∧ p5)) ∧ p4) ∨ p2))) ∧ (p5 ∨ False)) ∨ (p5 ∨ p4)) ∨ (True ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137496864809018250092066226247 : ((p5 ∧ (((((p2 ∧ (p1 ∨ (True → p5))) ∧ p4) ∨ (p3 ∨ (False ∧ (p3 → True)))) ∧ (p5 ∧ False)) ∧ (True → False))) ∨ ((True ∨ p4) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171986235160512793160506031676 : ((((((((p4 ∧ False) ∨ (True ∧ p1)) → False) → p2) ∨ p1) ∧ p2) ∨ (p3 → p4)) ∨ (((p1 → (p3 ∨ p4)) ∨ (p3 ∨ p4)) → (p2 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h6 =>
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233807236085767468658555956484 : ((p3 ∨ (p2 → p2)) → ((((False ∨ ((p2 → (p4 ∨ ((p1 ∨ p5) → p3))) ∧ ((p4 ∨ (p2 ∧ False)) ∨ p2))) ∧ True) → p1) ∨ (False → p3))) := by
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
theorem thm_5_vars_65315575209923416632623199552 : ((p3 ∨ (((((((p1 ∨ p2) → p2) ∨ p3) → ((True ∧ p5) ∨ p4)) ∨ (False ∧ (p4 → p5))) ∨ (True → False)) ∨ (p1 → (p4 → True)))) ∨ False) := by
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
theorem thm_5_vars_42970787898174879762786212699 : (((p5 → (((p1 ∧ p3) ∧ (((p3 ∧ (p1 → p4)) ∨ True) → (((p2 ∨ (False ∨ p4)) → p1) ∧ (p1 → p5)))) ∨ (p1 ∨ p5))) ∨ p5) ∨ False) := by
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
theorem thm_5_vars_21571440563774340971869232088 : (((True → (((p4 ∨ p5) ∧ (p3 → p5)) ∨ (p2 ∨ p4))) ∨ ((p1 ∧ (p1 ∧ (True ∧ (p3 → ((False → (p1 ∨ p1)) → p5))))) ∨ True)) ∧ True) := by
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
theorem thm_5_vars_765708256622546229725826349802 : (((p4 ∧ ((p4 ∨ ((False ∨ (p1 ∨ ((True ∨ p3) ∨ False))) ∨ p2)) ∧ ((p1 → p4) → (((p3 ∨ (p5 ∧ p4)) ∧ (p1 → p5)) ∧ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689301995553196464673587311595 : (((((((p4 → p4) → False) ∨ (((p4 → (True ∧ True)) → p5) ∨ p1)) ∧ (p4 ∧ p1)) ∨ ((p2 ∨ (p1 ∨ (True ∨ (True → p3)))) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608617726639816569943086688288 : (((((((p2 ∧ True) ∨ ((p2 ∧ (((True ∨ False) → p4) ∨ (p3 → (((p1 ∧ p1) ∧ p1) ∨ p5)))) ∨ p5)) ∧ (p2 → p1)) ∨ p4) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_113777924109746491789610354904 : ((((p4 ∨ (p4 ∧ p2)) ∧ (((False ∨ (p1 ∨ p5)) ∧ (p3 → p4)) ∨ (False ∨ (((p2 → p4) ∧ p4) → p5)))) → (True → p2)) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171665239079882430213808876248 : (((p4 ∧ ((p2 → ((((p5 ∨ p2) → False) ∧ (p2 ∧ p3)) ∧ True)) → False)) ∨ p2) ∨ ((False → (True → (p1 ∧ p5))) ∨ ((p3 → p4) ∧ p2))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134453044893229543157463257058 : (((((p1 ∧ ((p4 ∨ ((p3 ∨ p2) → ((True → (p5 → True)) → p3))) ∨ False)) ∨ (p3 ∨ (p2 → True))) ∧ p2) → False) ∨ ((p5 ∧ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_746367145505829300526230026156 : ((((p2 ∨ False) → (p5 ∨ (((p2 ∨ (False ∧ (True ∨ p3))) ∧ (((p2 ∨ p5) ∧ (p5 ∨ ((p5 ∧ p1) ∨ (p5 → p1)))) ∧ p3)) ∨ p2))) ∨ p1) ∧ True) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315435550025556534494844046963 : (p3 ∨ ((p2 ∨ (p4 ∧ True)) ∨ (((p5 ∨ p4) ∨ p3) ∨ ((((p2 → (p5 ∨ (False → ((p3 ∨ (p5 ∨ p3)) ∧ p2)))) ∨ p4) ∨ p4) → True)))) := by
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
theorem thm_5_vars_134970058032894887044471243154 : ((((p2 → (p5 ∧ ((True → p5) ∧ p2))) → ((p4 ∨ p4) ∨ ((p2 ∨ (True ∧ (p1 ∧ p2))) ∧ p1))) ∧ (True ∧ p3)) ∨ ((p2 ∧ False) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245150075323906197572658171910 : ((p2 ∧ True) ∨ (p2 → ((p4 ∧ ((((((((p5 ∨ True) ∧ (False → ((p2 ∨ True) → p4))) ∨ True) ∧ p3) ∧ True) → False) → p3) → p5)) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138702794620512060440968270806 : ((((((p5 ∨ p3) → (p1 ∧ False)) → (p2 ∧ p3)) ∧ ((p2 → False) ∧ (p4 ∨ ((p3 ∨ p2) → (True → p5))))) ∧ p2) → ((p2 ∨ p2) ∧ False)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h10.left
  let h13 := h10.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h13.left
  let h15 := h13.right
  -- Disjunctions on the left can always be decomposed.
  cases h15
  case inl h16 =>
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h17 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h11
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h18 := h14 h17
    -- False on the left can always be used.
    apply False.elim h18
  case inr h19 =>
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h20 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h11
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h21 := h14 h20
    -- False on the left can always be used.
    apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156815360247646443882253560870 : (((p2 ∨ ((p3 → (p3 → (p4 → p4))) ∧ ((((p3 → p5) → p1) → (p2 ∧ False)) ∨ False))) ∧ True) ∨ (p4 ∨ (p2 → ((True ∨ p3) → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313959721419324877252598465887 : (p3 ∨ (((((p3 ∨ p3) ∧ p2) ∨ ((False → ((((p2 → (False ∨ (p3 ∧ p1))) ∨ False) ∨ p1) ∨ True)) ∧ True)) → (p1 ∧ p5)) ∨ (False → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_866855708001894101094576016205 : (((((False → (False ∧ p2)) → (p1 → (False ∨ (((p1 → False) ∧ ((p4 → p1) ∧ p1)) ∨ ((p1 ∨ p4) → ((p4 ∨ p1) ∨ p2)))))) → p3) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False → (False ∧ p2)) → (p1 → (False ∨ (((p1 → False) ∧ ((p4 → p1) ∧ p1)) ∨ ((p1 ∨ p4) → ((p4 ∨ p1) ∨ p2)))))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63084969639054028692422286891 : ((p5 ∧ (((((((p2 ∨ p3) → (p4 → p3)) → ((False → True) → p1)) ∧ True) → ((p3 ∨ p3) ∧ p1)) ∨ ((p1 ∧ p3) → p1)) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774963342611271289417156687227 : (((False ∨ (((p1 ∨ p4) ∧ p5) ∨ ((((((p4 ∧ p5) ∨ False) ∨ (p5 ∧ p5)) ∧ p2) → ((p4 ∨ ((p5 → True) ∨ p2)) ∨ p3)) ∨ p3))) ∨ p3) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h8 =>
      -- False on the left can always be used.
      apply False.elim h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50279827663945856056877363321 : ((((p3 → (((False ∧ p2) ∨ ((p2 ∨ ((p5 → (p2 ∧ p1)) ∧ p4)) → p2)) ∨ p3)) ∨ (p5 ∧ p4)) ∨ ((p5 ∧ (False → False)) ∧ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669031706841857493047827445973 : (((((((False ∨ (True ∨ True)) ∨ ((p1 ∨ p5) ∨ ((False ∧ p1) → ((p2 ∧ p4) → (p3 ∨ p2))))) ∨ p1) → False) ∨ (p2 → (p2 ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213786111112495144047168839224 : (((p1 ∧ (p2 ∧ p5)) ∨ p4) ∨ (p1 → (((((p1 → (((p2 ∨ p1) ∨ (p5 ∨ p1)) ∨ True)) → p4) → p4) → True) → ((p4 → p5) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709678408394443368755325899 : (((((p4 → True) ∨ p4) ∧ (p2 ∧ (p3 ∨ False))) ∧ ((((p3 → p3) ∨ p2) → ((True ∨ p3) → (p3 ∨ p4))) ∨ (False → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_595666730672200431959212812510 : (((((p4 ∧ ((p4 ∨ (True ∨ p5)) ∧ (p5 ∨ ((p4 → p4) ∧ p5)))) → ((p5 → (p3 ∨ (((p5 → p3) ∧ p1) ∧ True))) ∨ p1)) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709712532225543842013360691727 : ((((True → (((p4 ∨ p2) ∨ (p3 ∨ False)) → p1)) → ((False ∨ p1) ∨ (((((p1 ∧ p5) ∨ (p2 → p5)) ∧ (p1 → p5)) ∨ p5) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_514296785652162576358473533845 : ((((p3 ∨ False) ∨ (((((((p3 ∧ ((True → p1) ∨ False)) → False) → (False ∧ p4)) ∨ p5) → ((p2 → p3) ∧ False)) ∨ (p1 → True)) ∨ p4)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340734453097153657673018521024 : (p2 → ((((p3 ∧ (p5 ∨ (p3 ∨ (p1 ∨ (((p4 ∧ False) ∧ False) ∨ ((p1 ∨ ((True ∨ p4) ∨ (p1 → p1))) → p1)))))) ∨ p3) ∨ p2) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183994544362203840118771280757 : ((((p4 ∧ ((p3 ∨ (p3 ∨ (p2 → p4))) ∧ p4)) ∧ False) ∨ True) ∨ ((False ∨ ((p5 ∧ (p2 ∧ True)) ∨ ((p4 → p2) → p4))) ∧ (p3 → p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336285964907925149008880326118 : (p1 → ((((p1 → p3) ∨ (p1 → ((False ∨ p3) ∧ (p4 → p5)))) → (((((False ∨ False) ∨ p4) ∨ ((p1 ∨ p3) ∧ True)) ∧ True) ∨ p1)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_53282767234095609840944539421 : (((p4 ∧ ((True → True) ∧ ((p3 ∨ ((p3 ∧ p4) → p2)) ∧ p5))) ∨ ((p5 ∨ ((p4 ∨ p3) ∧ ((p4 → (True ∨ p3)) ∨ False))) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165796994417716671075073602616 : ((((p4 ∨ p5) ∧ p1) ∧ ((p5 ∨ (((p2 ∨ (True → p2)) ∧ p3) ∧ (p2 ∨ p3))) ∧ p5)) ∨ ((False ∧ False) → ((p2 → (p5 → False)) ∨ True))) := by
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
theorem thm_5_vars_115081363328629453406679537963 : (((p3 ∧ ((True → p4) ∨ ((True ∨ ((p1 ∨ p5) ∧ p2)) ∧ p3))) ∨ ((p1 ∨ ((True ∨ (p1 → False)) → p5)) ∨ (p1 ∨ p4))) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_765759159531014263936206414417 : (((p4 ∧ (((((False ∨ True) ∨ p1) → (False ∨ p3)) → False) ∧ ((p4 → (((False ∧ p4) ∧ ((p2 → True) → (p4 ∨ p1))) ∧ True)) ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_723688865156749787004980985141 : (((((True → False) → False) ∧ (p3 → (True → (((((p2 ∨ (p1 ∧ (((p2 ∨ p4) → p3) ∨ False))) ∨ p4) ∧ True) → p2) ∧ (p5 ∧ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_960603585187379283821233857049 : ((((True ∨ p3) ∧ (((False ∨ p1) → (False ∨ True)) → (((((p4 → (False ∨ (p5 ∧ False))) ∧ p2) ∨ ((False ∨ False) ∨ p1)) → p2) ∧ p4))) → p4) ∧ True) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : ((False ∨ p1) → (False ∨ True)) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- False on the left can always be used.
        apply False.elim h7
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h9 := h3 h5
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h12 : ((False ∨ p1) → (False ∨ True)) := by
      -- Implications on the right can always be decomposed.
      intro h13
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- False on the left can always be used.
        apply False.elim h14
      case inr h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h16 := h3 h12
    -- We need to get the right conjuct of h16 based on <expert-advice>.
    let h17 := h16.right
    -- One of the premise coincides with the conclusion.
    exact h17
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41599120616237131150882228849 : (((((p4 ∧ (((False ∨ True) ∨ p1) ∨ p2)) ∨ p2) ∨ (p2 ∨ (((p5 ∨ p4) ∨ False) → (p4 ∧ (p2 ∨ (p5 ∧ (True → p1))))))) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346892019618602030902325336680 : (p3 → ((((((p4 ∧ (((p3 ∧ p3) → False) ∨ ((p1 ∧ p5) → p3))) ∧ p5) ∨ p1) ∧ p2) ∧ p2) ∨ (((p1 ∧ (p4 ∧ p1)) → p3) ∧ p3))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246419303330137086613255717992 : ((p5 ∧ True) ∨ (p1 ∨ (((True ∧ p3) ∨ (p4 ∧ p3)) ∨ (p1 → ((p3 ∧ (p2 ∧ (p3 ∨ (True → (p2 ∧ False))))) → ((p3 ∨ p5) ∨ p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114147235119346387032043725825 : ((((((p3 ∧ p4) ∧ ((p4 ∨ p3) → (((p1 ∧ (p5 → p1)) → p3) ∧ (p2 ∧ p2)))) → p5) ∨ p3) → (p1 ∧ (p1 → p1))) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114310419332643309869636044593 : (((((((p1 ∨ p4) ∨ p4) → p4) ∨ p2) ∨ (((p2 → True) ∨ (p3 → (p4 ∧ p5))) → p5)) ∧ ((p2 ∧ p2) → (p2 ∨ True))) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53427831055447081030338474899 : ((((True ∧ (p4 ∧ (p5 ∨ p3))) ∧ (p3 ∨ (p1 ∨ (p3 → p4)))) → (((False ∨ ((p1 ∧ (False ∨ False)) → (p5 → p1))) ∨ p4) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314114488954655084777918978886 : (p3 ∨ (((True → p3) ∧ (((True → False) ∨ ((p5 ∨ (((p1 → p1) ∨ (p1 ∧ (p1 → True))) → False)) → p2)) → (p4 → p2))) → (p3 ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118534649625227759371977960126 : ((p3 ∨ (p3 ∧ ((True → p5) ∨ ((((True → (True ∧ p4)) ∧ (p2 ∧ p1)) ∧ (p4 ∨ (p1 → ((True ∧ False) ∨ p2)))) → p5)))) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300050495062740539343471120302 : (False ∨ (((((((p1 ∨ (False → p2)) ∧ ((p2 ∨ p5) → ((p2 ∨ p5) → False))) → (p3 ∨ (p3 ∧ p1))) ∧ False) ∨ p3) ∧ p3) ∨ (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609354981213448370900569074351 : ((((((p1 ∨ p5) ∨ ((True ∨ (True ∨ p3)) → (p5 ∧ ((((p4 ∧ p4) ∧ ((p3 ∨ p3) ∨ True)) ∧ (False ∧ False)) → p1)))) ∨ True) ∨ p1) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_199777243933586835522521974415 : (((p4 → ((True ∨ (p1 ∧ False)) → p1)) → True) → (p1 ∨ (p4 → (p1 ∨ (False ∨ (p5 → (p5 ∧ ((((p2 ∨ p2) ∧ False) ∨ True) ∨ p4)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698548603167583715253325973949 : ((((((p5 → p1) ∧ (p1 ∧ p5)) ∨ ((p5 → (p3 ∨ p2)) → p3)) ∨ ((p2 ∧ (True → p5)) → ((p2 ∨ p4) ∧ ((False ∨ True) ∧ True)))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311268447463439466567200006445 : (p2 ∨ (True ∧ (((((((False → True) ∨ (p2 ∧ p4)) ∨ (((p4 → p1) → (False ∧ False)) → (p5 ∨ p4))) ∨ p5) → p4) ∨ True) ∨ (p2 ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_190175547261163950451713341818 : (((p4 ∧ ((False → (False → (False ∨ p2))) ∧ p3)) ∧ True) ∨ (((p3 ∨ (p1 → (False ∨ p3))) ∧ ((p1 ∨ (p3 ∨ True)) ∧ (False ∨ False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59966894242252027972813328317 : (((True ∨ p5) → (p1 ∧ (((True ∨ True) → ((p2 ∨ p4) → (p5 ∨ ((p2 ∧ p5) ∨ p5)))) ∧ (p3 ∨ ((p4 ∨ (True ∧ p5)) ∨ p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41244078893208319772226306732 : (((((p5 ∧ ((p3 ∧ (((p4 ∨ p2) ∨ p3) ∧ (False → p1))) ∧ ((p3 ∨ p5) ∧ p5))) ∧ True) ∨ ((False → (p2 ∧ p2)) ∨ p2)) ∨ p3) ∨ False) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135848196291653972230982580711 : (((False → (((p3 ∧ p1) → p3) ∨ (((p4 ∧ p2) ∨ p2) ∧ p4))) ∧ ((((p2 ∨ (p4 ∧ True)) ∧ p2) → p1) → p3)) ∨ (False → (p2 ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117655565648475592479299630343 : ((p3 ∧ ((((p3 ∧ (p3 ∧ (((p1 ∨ (False → (p3 ∨ (True ∧ (True → p3))))) ∧ True) ∧ p1))) ∧ p4) → p1) → (p5 → p4))) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218194783193084000315864234374 : (((p2 ∧ False) ∨ (False ∨ p4)) → ((False ∨ True) ∧ ((((((p3 ∧ (p1 ∧ p2)) ∨ (p4 → ((False ∨ p2) ∨ p1))) ∧ p4) ∧ p1) ∨ p4) ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h13
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- False on the left can always be used.
    apply False.elim h16
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h18 =>
      -- False on the left can always be used.
      apply False.elim h18
    case inr h19 =>
      -- One of the premise coincides with the conclusion.
      exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_674987658870784269724243855871 : ((((((p4 → (p3 ∨ p1)) ∨ (((((True ∧ p2) ∨ p2) → p3) ∧ p1) → (p2 ∧ (p4 ∨ False)))) ∧ p1) ∧ (((p2 ∧ False) ∨ p4) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64678792571236752915076699524 : ((p1 ∨ (p3 ∨ ((False ∨ True) → (((p1 ∨ (p3 ∨ (((True → False) → ((p4 ∧ p3) → False)) → True))) ∨ ((False → p1) → p4)) → False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232165849717590344611566122556 : (((True → p4) → p3) → ((((p5 ∧ (p5 ∨ True)) ∨ (p4 → ((((((p4 → p1) → p1) → True) ∧ p1) → (p2 ∧ False)) → p3))) ∨ p2) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : (True → p4) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h4
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_666877162480317578913011518805 : (((((((False → (p4 ∨ p5)) → False) ∨ p5) ∨ (p2 ∧ (((True ∧ ((p3 ∧ p3) ∧ p5)) ∧ p1) → (p3 ∧ p2)))) ∧ (True ∧ (p2 ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178291129159507553114651358443 : (((p1 ∨ (False ∧ (True ∧ ((p3 ∨ p2) → (p5 → p1))))) ∧ (p5 ∧ p5)) ∨ ((p2 → ((((p2 → True) ∧ p1) ∨ p2) → True)) ∨ (p4 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157755371776980148179883406111 : ((((p3 ∧ (p4 → p3)) ∧ ((((p5 ∧ p4) ∨ False) ∨ True) → p3)) ∧ ((p1 ∧ p4) ∧ (p4 ∨ False))) ∨ (((True ∨ p1) → p5) → (p4 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (True ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346766542571019975810736926978 : (p3 → ((((((p3 ∨ p4) → ((p3 → ((True ∧ (p5 ∧ p5)) → (False ∨ p1))) ∨ p2)) ∨ True) → p1) ∨ False) ∨ ((p1 → False) ∨ (p4 → p3)))) := by
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
theorem thm_5_vars_43325365253724916307231798911 : (((((((p1 → (True → (((p1 ∨ (p3 ∧ p1)) ∨ (p4 ∨ False)) ∨ (True → p5)))) ∨ ((p3 → p4) ∨ p3)) ∧ p3) → p3) ∨ False) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111717522029530603857867907648 : ((((((p2 ∧ (False ∨ (p1 ∧ p5))) ∨ False) ∧ ((p2 → ((p4 ∨ (((p1 ∧ False) ∧ p1) ∧ p3)) ∨ p1)) ∧ p1)) → p3) ∨ p4) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



