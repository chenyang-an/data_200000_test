variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251535708761663513069026159890 : ((p3 → False) ∨ ((((p1 ∧ (p3 → p5)) ∧ ((((p5 → (((False → True) ∧ p1) → (False → p5))) ∨ False) ∧ (p1 ∨ True)) → p3)) ∧ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225117118852467038035133709624 : (((p2 ∧ p4) ∧ True) ∨ ((False ∧ (p1 ∧ (((((((True → p5) ∨ p5) ∧ p2) ∨ p2) ∨ ((p5 → p2) → p5)) ∨ p2) ∨ p1))) ∨ (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173046853817349398735739279704 : ((False ∨ ((p5 ∧ ((p4 ∨ (((p3 ∨ (p3 → p3)) ∧ p4) ∧ p3)) ∧ p4)) ∧ p5)) ∨ (((p2 ∧ (p3 → True)) ∨ (True → (p4 ∧ p4))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_804463166796803587812383207507 : (((p3 → ((((p5 ∨ ((p2 ∧ p1) ∧ p5)) ∨ p4) ∨ p4) ∨ (p3 ∧ (((False ∨ ((False ∧ p1) → p3)) ∨ ((True → p2) ∨ p1)) ∨ p5)))) ∨ p2) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_37937283218304993251612556533 : ((((p1 ∨ ((False ∧ (p3 ∧ ((p4 ∨ p4) ∧ ((p3 → (p4 → (p3 ∧ (p3 ∨ p4)))) → (p4 ∧ p1))))) ∧ p2)) ∧ (p3 → False)) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51023901806823589366587327162 : (((p3 ∧ (((p4 ∨ (((False ∧ False) ∧ (p1 ∧ True)) ∨ (True → (True ∨ p2)))) ∨ p1) → p3)) ∧ (((True → p4) → p2) ∧ (True → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_784922393613015275832261553597 : (((p3 ∨ (p3 → (((p1 → (True ∨ ((((True ∨ p1) ∧ True) ∧ (True ∨ (((p5 → True) ∨ p5) ∨ (True ∧ p5)))) → p5))) ∨ p1) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134627087818967356848180201634 : (((((p1 ∨ ((((False → ((False → p4) ∧ p1)) → p2) ∧ p4) ∨ False)) → p4) ∧ (p4 ∧ ((True ∨ False) → p2))) → p1) ∨ (p3 → (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_79538540719617963378227279221 : (((((p2 ∧ (((p3 ∧ p2) ∨ ((False ∧ p3) ∨ p1)) → (p4 ∨ p5))) ∨ True) → ((p4 ∧ (p4 ∨ True)) ∧ (p5 ∨ p1))) ∨ (p4 ∨ False)) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : ((p2 ∧ (((p3 ∧ p2) ∨ ((False ∧ p3) ∨ p1)) → (p4 ∨ p5))) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h4 := h2 h3
    -- We need to get the left conjuct of h4 based on <expert-advice>.
    let h5 := h4.left
    -- We need to get the left conjuct of h5 based on <expert-advice>.
    let h6 := h5.left
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214575880331583991085271731700 : (((p2 ∨ p4) ∧ (p4 → p3)) ∨ ((False ∧ ((p4 ∧ (p1 ∧ (p4 ∨ ((True → False) ∨ (p4 ∨ (p2 → False)))))) ∧ p2)) ∨ (p5 → (True ∨ p3)))) := by
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
theorem thm_5_vars_135859413894373168145932201750 : ((((p2 → (((p5 → True) → p3) ∨ (p4 → (p1 ∧ p2)))) ∨ p2) ∨ (((p3 ∧ p5) ∧ p3) → ((p3 → p5) → p1))) ∨ ((True ∧ False) → p4)) := by
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
theorem thm_5_vars_118357825598705407053251705581 : ((p2 ∨ (((p5 → ((p5 ∨ p1) ∧ ((True → (p3 ∨ p4)) → ((True ∧ (p1 ∧ p3)) ∨ (True ∧ p3))))) ∨ p3) ∧ (p4 → p4))) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346354965447407200196272126022 : (p3 → (((p5 ∧ (p2 → p4)) → ((p5 ∨ (p4 ∧ (((p5 → p2) → (p4 ∧ (p4 → ((p1 → p4) ∧ True)))) ∨ p5))) → False)) ∨ (False → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159315523987747167870016826107 : ((p5 → (((((True → p2) → p3) ∧ (p5 ∨ (p1 → p1))) → (p3 ∧ p2)) ∧ (p4 ∧ (True ∧ p5)))) ∨ (p5 → (p5 ∨ (False ∧ (False → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695713152451372970245006191285 : (((((((p3 ∨ p1) ∨ p2) ∧ p3) → (p4 ∨ (p1 → ((False → p4) ∧ p1)))) → (p4 ∧ ((True ∨ p5) ∨ (p3 → (False ∧ (p3 ∧ False)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245265890918216979304720914880 : ((p2 ∧ p1) ∨ (p2 ∨ (((((True ∧ True) ∨ (p2 ∨ p1)) ∧ (p3 ∧ p2)) ∨ ((p5 ∧ True) → ((p1 ∧ ((True ∨ p2) ∧ p4)) ∨ True))) ∨ p2))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51522509038650699803856372037 : ((((False → False) ∨ (((p2 ∨ p4) → p2) → (((False ∨ False) ∨ p3) ∧ ((False ∧ False) → True)))) → ((((p1 ∧ p1) ∨ p2) ∧ p2) ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_341963809651025560056400917393 : (p2 → (((p1 ∧ ((p4 ∧ (p4 ∨ p4)) ∨ (p3 → (((p2 ∧ (p3 ∧ p2)) ∧ p4) → (p1 ∧ (True ∨ False)))))) ∧ p3) ∨ (p2 → (p5 → True)))) := by
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
theorem thm_5_vars_266245056037070020948558340519 : (True ∧ (p5 → ((p4 → ((True → (((True → ((p1 → p2) ∨ p4)) ∧ ((((p3 → (p3 → False)) ∨ p4) ∧ p4) ∨ True)) → False)) ∨ p3)) ∨ True))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114552813262386656462624714906 : (((((p2 ∧ (((p4 ∨ False) → False) ∨ ((True ∧ p1) ∨ True))) ∨ (p4 ∨ p2)) ∨ p1) ∧ ((p2 ∨ p3) ∧ (p2 → (p2 → p3)))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161448440966158409880439469342 : ((p2 ∧ (p2 → (((((True → True) → ((p2 ∨ p4) ∨ p3)) → p5) ∧ ((p5 ∧ p4) → False)) ∨ False))) → (((p2 ∨ p1) → (p4 → p2)) → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h10 : ((True → True) → ((p2 ∨ p4) ∨ p3)) := by
      -- Implications on the right can always be decomposed.
      intro h11
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h12 := h8 h10
    -- One of the premise coincides with the conclusion.
    exact h12
  case inr h13 =>
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116529547297601067350015738598 : (((True ∨ p1) ∧ ((p3 ∨ ((p2 ∧ (p1 ∧ (((p2 ∧ p4) → p3) ∧ ((p3 → ((p2 → True) → p4)) → p3)))) → p4)) ∨ p1)) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_88176387886499010214633896770 : ((((p1 ∨ p5) → (p2 ∧ p5)) ∧ ((((((p2 → ((p4 ∧ True) → p3)) ∨ p2) → p2) ∧ (p2 ∨ p5)) ∨ ((p5 ∨ p1) → True)) → False)) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (((((p2 → ((p4 ∧ True) → p3)) ∨ p2) → p2) ∧ (p2 ∨ p5)) ∨ ((p5 ∨ p1) → True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611015759993405171367480835758 : (((((((p1 → p4) ∧ ((p3 ∧ p2) → p3)) ∧ (p3 → (p2 → (((p1 → ((False → p5) → p1)) ∨ (p1 → p2)) → p5)))) → p1) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_166522174876900540419544354191 : ((p4 ∨ (((p1 ∨ False) ∨ p1) ∨ (p2 ∨ (p3 ∨ (((p2 ∧ p1) ∨ p3) ∨ (p1 ∨ True)))))) ∨ (((p1 ∨ p5) → ((p2 → p4) → p1)) ∧ p1)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118124495676928990461593356103 : ((False ∨ ((((p2 ∧ (((((p4 ∨ p1) ∨ p5) ∧ p1) → (True ∧ ((False ∧ p1) ∨ p1))) → False)) ∧ p5) ∨ p1) ∨ (p5 ∨ True))) ∨ (p3 ∨ p1)) := by
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
theorem thm_5_vars_49563417112939895106004234283 : (((((p3 ∨ (((False ∧ (p2 → True)) ∨ (True ∨ p3)) → (True → (p3 ∧ p1)))) → p2) → (p3 ∨ (p3 ∨ p2))) → (p1 → (p1 → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325734456763136057690875759833 : (p5 ∨ (p2 ∨ (((((((False ∧ False) ∨ True) ∧ (p2 ∨ ((p4 → p4) ∧ False))) → False) → p5) → (p5 ∨ (((p4 ∧ p1) ∨ p4) ∧ p1))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_730079975599579977688972123083 : (((((p2 ∨ p3) → p5) → ((p3 ∨ (p2 ∨ (p5 ∧ p1))) → (p5 ∧ ((((p4 ∨ ((False ∨ True) ∧ (p3 ∧ p4))) ∨ p5) ∧ False) ∨ p5)))) ∨ p3) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h4 : (p2 ∨ p3) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h5 := h1 h4
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h8 : (p2 ∨ p3) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
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
      -- One of the premise coincides with the conclusion.
      exact h11
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h14 : (p2 ∨ p3) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h13
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h15 := h1 h14
    -- One of the premise coincides with the conclusion.
    exact h15
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h18 : (p2 ∨ p3) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h17
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h19 := h1 h18
      -- One of the premise coincides with the conclusion.
      exact h19
    case inr h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h21
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67620496022838188401455199905 : ((p1 → (p4 ∧ ((p4 ∧ p4) ∧ ((p2 → (p4 → p5)) → (((((p4 ∧ p5) ∨ p2) ∨ p5) ∨ (p4 ∧ (True ∧ (True → p4)))) → False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111650808892532103930441026377 : (((((True ∧ False) ∨ ((p2 ∧ (p4 ∨ (False ∧ (p2 ∨ True)))) ∧ ((p5 ∨ True) ∨ (True ∧ ((p1 → False) → False))))) ∨ p5) ∨ p3) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62978787307584054250110138127 : ((p4 ∧ (p3 ∨ (p3 ∧ ((((p3 ∧ (p4 → p5)) → p3) → ((p4 ∧ (p2 ∧ p1)) ∧ True)) ∨ ((True → (p4 ∨ (p2 → p2))) ∧ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_750367040993587644724709773882 : (((True ∧ ((True ∨ (((True ∨ ((p5 ∨ (p4 → (p4 ∧ (((True ∧ p4) → p2) ∨ False)))) ∨ (p5 ∧ p3))) → p4) ∨ p1)) → (p4 ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114946873038654698393462588786 : ((((p4 ∧ p5) ∨ ((p4 ∧ (p5 → (p1 ∧ (p4 ∧ p2)))) ∨ (p5 → p1))) → (True → (((p4 → p1) → (True ∧ p1)) → p5))) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161578332906822003800951105454 : ((True ∨ ((p5 ∧ (((False ∧ p2) ∨ (p3 ∨ ((p5 ∨ p4) ∧ p3))) ∧ p2)) → ((p3 → p5) ∨ p3))) → ((p3 ∨ ((p4 ∨ p1) ∧ p5)) ∨ True)) := by
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
theorem thm_5_vars_671300452241153326566845717924 : ((((p5 ∨ (p4 ∧ ((((p4 → True) ∧ p2) ∧ (p2 ∧ False)) ∨ ((p1 ∧ ((p4 → p4) ∨ p5)) ∨ (p2 ∧ p3))))) ∨ ((p1 → p2) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610799964077932881424121250623 : ((((((((p1 → (p4 ∧ p5)) ∨ ((p4 → (p4 ∧ p3)) ∨ ((p2 ∧ p2) ∧ p4))) → p4) → ((p3 → (p1 ∨ p1)) → True)) → p4) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_178755110947583313974586492374 : ((((p5 → True) ∧ p5) ∧ ((((p2 ∧ (p3 ∨ False)) ∨ False) ∨ True) ∧ p2)) ∨ (((((p2 → p3) ∨ p1) → p3) → ((p2 ∨ True) ∨ p1)) ∨ False)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173072526100291608689737987842 : ((False ∨ (p1 → ((p5 ∧ (((p5 ∨ p4) ∨ (p2 ∨ False)) ∨ True)) ∨ (p5 → p5)))) ∨ (p5 ∨ ((False → (((p5 ∨ p4) → p4) ∨ p1)) ∧ False))) := by
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
theorem thm_5_vars_207721402829955401952880291501 : (((p2 ∧ (p2 ∧ (p5 ∨ p1))) → p3) → ((True ∨ ((p5 ∨ (p4 ∨ (p5 ∧ p5))) ∧ (p3 ∨ (p1 → (p5 → (p4 ∨ p1)))))) → (p4 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h12 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h11
        case inr h13 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h11
      case inr h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h17 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h18 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233570414535227549937249715595 : ((p1 ∨ (p2 → p1)) → ((p1 ∧ (p5 ∧ (p4 → ((False ∧ True) ∧ (False ∨ p4))))) ∨ ((((True ∧ (p1 → True)) ∨ (p2 → p1)) → True) → True))) := by
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
theorem thm_5_vars_326160177704929780029952810382 : (p5 ∨ (p2 → (((((p1 ∧ True) ∨ p5) → p1) ∧ (((((p3 ∧ (((p2 → p4) ∨ (p3 → False)) → p1)) ∧ p4) ∧ p4) → p5) ∧ p5)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62248657190395023357054209955 : ((p3 ∧ ((False ∧ ((((((((p1 → (p5 ∨ p1)) → p4) → False) → (p2 ∨ p3)) → (p2 → (False → False))) ∨ p5) → p2) ∧ p2)) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113782062627673190483843045140 : ((((p3 → (p1 ∨ p3)) ∨ ((((p4 ∨ (p4 → (p3 ∨ (p1 → (False ∨ True))))) ∨ p2) → (p5 ∧ p3)) → p4)) → (p3 ∧ p1)) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122892232725631344466311858849 : (((True ∧ (p3 ∨ (((False ∧ (((True ∧ p4) → (p3 → p1)) ∨ (p4 → p3))) → p5) ∨ (True ∨ p4)))) ∧ (p5 ∧ (p5 ∨ p4))) → (False ∨ True)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
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
      let h13 := h3.left
      let h14 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- Conjunctions on the left can always be decomposed.
        let h19 := h3.left
        let h20 := h3.right
        -- Disjunctions on the left can always be decomposed.
        cases h20
        case inl h21 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h22 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h23 =>
        -- Conjunctions on the left can always be decomposed.
        let h24 := h3.left
        let h25 := h3.right
        -- Disjunctions on the left can always be decomposed.
        cases h25
        case inl h26 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h27 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347468573543214867751333509876 : (p3 → ((((p2 ∨ p1) ∧ (p5 ∨ p1)) ∧ p2) ∨ ((((p3 ∧ (True ∨ ((p2 ∧ p1) ∧ False))) ∨ (p2 ∧ ((p1 ∨ p4) ∨ p4))) → False) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148382636419304313559377769246 : ((((((p5 ∨ p5) ∨ p5) → (True → p2)) ∧ ((p2 ∧ (p3 → False)) ∨ p3)) ∨ (p4 ∧ (False ∧ (p3 → p4)))) ∨ ((p4 → p1) ∨ (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200130204332487254026404185394 : (((False → (True → p3)) ∧ (p1 → (p4 ∨ p3))) → (((p5 ∨ (p3 ∧ p1)) ∧ p2) ∨ (True ∨ (True ∨ (p5 ∨ ((p2 ∨ p4) → (p4 ∧ p5))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354830598067919047203558649935 : (p5 → (((p5 ∨ (p5 → p2)) → ((p4 → p4) → (p4 → (((((False ∨ p4) ∧ (False ∨ p5)) ∧ p3) ∨ (False → (False ∨ p4))) ∨ True)))) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h2
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
theorem thm_5_vars_302860948050445001476811799541 : (False ∨ (True → (((((False ∨ p1) → True) → (p2 ∨ (((p2 → ((p2 → (p4 ∨ False)) ∨ p1)) ∧ (p2 ∧ p4)) ∧ (p5 → p1)))) → p1) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608311801595342512755834096259 : ((((((((p4 → p5) ∨ ((p3 → (p3 ∧ p4)) → (False ∨ p4))) ∨ ((p5 ∧ p1) ∨ ((p1 ∨ (p2 ∨ p5)) ∨ p4))) ∨ p2) ∨ p5) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42664523066753125532555525482 : (((p4 ∨ ((p3 ∧ (((p1 ∨ True) ∨ True) ∧ True)) ∧ (p2 → (((p4 ∨ ((p2 ∧ True) → False)) ∧ False) ∨ (p3 ∨ (p3 → p3)))))) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219899337221098786188667264879 : ((p4 → ((p3 → True) ∨ p4)) → ((p1 ∨ ((True ∧ p4) → p3)) ∨ (True ∨ (((p2 ∨ p1) ∧ (False ∧ p1)) ∨ (((p4 ∨ p3) ∧ p3) ∨ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246301091978757043811745396523 : ((p4 ∧ p4) ∨ (p5 ∨ ((p3 ∨ (p3 ∧ True)) ∨ (((True ∨ (p4 → ((True ∧ False) ∧ p5))) → True) ∨ (p2 → ((p4 ∧ (p4 → True)) → p1)))))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153929841418917312190815117412 : (((((p1 ∧ ((p3 ∨ ((p2 ∧ True) ∧ p2)) → (p2 ∨ False))) ∧ (p1 ∨ p1)) ∨ (p1 → p1)) ∧ True) ∧ ((p3 → (p1 → (True → p3))) ∨ p2)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621124880466977670683761193640 : (((((p4 → p3) → (((p2 → False) → p5) → (p5 ∨ (True ∧ (((p3 ∧ (False ∨ ((p1 ∨ p1) ∧ (p3 → p2)))) ∨ True) ∨ p1))))) ∨ p4) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178427163293963270349016920808 : (((p5 → ((p1 ∧ (((p1 ∧ False) ∧ p2) → p4)) ∨ False)) → (p4 → p1)) ∨ (p1 ∨ (p4 → (False ∨ ((True ∨ p2) ∨ (p2 → (p2 → p3))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_310339403314371326088620800010 : (p2 ∨ ((p2 ∧ ((((False ∨ p3) → p5) ∧ (p3 → p1)) ∨ True)) → ((((p5 ∧ p3) ∧ (p1 ∧ p4)) ∧ ((p4 ∨ p1) ∨ False)) ∨ (False → False)))) := by
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
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118890597112352880678000518454 : ((True → (p4 ∧ (p1 ∧ (True → (p1 → ((False ∨ ((((True ∧ p5) ∨ (p4 ∨ False)) ∧ p2) ∨ (p5 ∨ (True ∨ p5)))) ∧ True)))))) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197135361987764968518999439777 : (((p5 ∨ (False ∧ ((p4 ∨ p4) ∧ p1))) ∨ True) ∨ (((((p1 ∨ (False ∧ True)) → (((p2 → p4) → (p4 ∧ p2)) ∨ p2)) → True) ∨ p4) → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_958235039338315142399732894703 : ((((p2 → (p5 ∨ p2)) → ((((False ∧ (p4 ∨ ((p4 ∨ True) ∨ (((True ∨ p2) ∧ p1) ∧ p2)))) ∨ (p3 ∧ False)) → p5) ∧ (p2 ∧ False))) → False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 → (p5 ∨ p2)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338348787619199731638122932595 : (p1 → ((((p2 ∨ p4) ∧ False) ∨ p4) ∨ (((p1 → ((False ∧ False) ∧ (p5 ∧ False))) → (((p5 ∨ p3) ∧ p4) → (p2 ∨ p2))) ∨ (p1 ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_762916878674506191040889845375 : (((p3 ∧ ((True → (((p5 ∧ p4) ∨ True) ∧ p5)) → (((True ∧ ((False ∨ (True → p1)) ∧ (p1 ∧ (True ∧ (p3 ∨ p3))))) ∧ p2) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165985077492173062904942478395 : (((False ∧ p3) ∨ (((p4 ∧ p3) ∧ ((((p3 → p3) ∧ p4) ∧ (p4 ∧ True)) ∧ p3)) ∨ True)) ∨ ((((p4 → True) ∧ False) → p4) ∧ (False → False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306578680578893783310456215621 : (p1 ∨ ((p4 ∨ p2) → ((((p2 ∨ (p4 ∧ (p4 ∧ ((p5 ∨ ((p4 ∧ True) → p2)) ∧ p3)))) ∨ (p1 ∨ (p3 ∨ p2))) → (p4 ∧ p4)) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h13 =>
          -- One of the premise coincides with the conclusion.
          exact h9
        case inr h14 =>
          -- One of the premise coincides with the conclusion.
          exact h9
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h17 =>
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h18 =>
          -- One of the premise coincides with the conclusion.
          exact h2
        case inr h19 =>
          -- One of the premise coincides with the conclusion.
          exact h2
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h21 =>
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h22 =>
        -- Conjunctions on the left can always be decomposed.
        let h23 := h22.left
        let h24 := h22.right
        -- Conjunctions on the left can always be decomposed.
        let h25 := h24.left
        let h26 := h24.right
        -- Conjunctions on the left can always be decomposed.
        let h27 := h26.left
        let h28 := h26.right
        -- Disjunctions on the left can always be decomposed.
        cases h27
        case inl h29 =>
          -- One of the premise coincides with the conclusion.
          exact h25
        case inr h30 =>
          -- One of the premise coincides with the conclusion.
          exact h25
    case inr h31 =>
      -- Disjunctions on the left can always be decomposed.
      cases h31
      case inl h32 =>
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h33 =>
        -- Disjunctions on the left can always be decomposed.
        cases h33
        case inl h34 =>
          -- One of the premise coincides with the conclusion.
          exact h2
        case inr h35 =>
          -- One of the premise coincides with the conclusion.
          exact h2
  case inr h36 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h36



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_665518455354658478527670790564 : ((((((True ∧ ((True ∧ ((((p2 ∧ p2) ∨ p4) → (False → (p3 ∧ False))) → (p5 ∨ p3))) ∨ p3)) → p4) ∨ True) ∧ ((p4 ∨ p4) → p4)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774047771590225167862180832373 : (((False ∨ (((((True ∧ ((((False ∨ p4) ∧ (p4 → p1)) ∨ p4) → (False ∧ (False → (p3 ∧ p4))))) ∧ p2) ∧ p5) → p1) ∨ (False → p1))) ∨ p2) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611204617334159081123365060159 : ((((((False → (True ∧ p5)) → (((p2 → ((((p5 → (True ∧ True)) → (False ∨ p5)) ∧ p5) ∨ (False ∧ p5))) → p3) → p4)) → p1) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_244519229140964355972591343718 : ((False ∧ p3) ∨ (((p1 → (p3 ∧ (p2 ∧ p2))) ∧ p2) → ((p5 → False) ∨ (False → (True ∧ ((p4 → p5) → (((p5 → p5) ∨ True) ∨ p4))))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59063552978118225540593750107 : (((p5 ∧ True) ∨ (((((((((p3 → p5) ∧ p3) → p5) ∨ p2) ∧ (p5 → (p3 → False))) ∧ (p4 → p5)) ∨ (p2 ∧ p1)) ∨ False) ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354635443834647149506899303599 : (p5 → (((p4 → ((p4 ∧ ((p3 ∨ p4) ∧ ((p1 ∨ ((((p4 ∧ (False ∧ p5)) ∨ (p1 ∨ True)) ∨ True) → False)) → p3))) ∨ p5)) ∨ True) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148422359834629219194007262539 : (((((True ∧ (p2 → False)) ∧ (p1 ∨ p1)) ∧ (False → ((p1 → p1) → p2))) → ((p1 → p1) ∧ (p5 → p2))) ∨ ((p3 ∧ (True ∧ False)) → p1)) := by
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
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114393565737472581549661667540 : (((((False → p5) → (p2 → (p4 → (((p1 ∧ p3) ∧ False) ∨ p3)))) ∨ (True ∧ (True ∧ True))) ∨ (False → ((True ∧ True) ∧ p1))) ∨ (p3 ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50247624579269665495182408711 : (((((p5 ∨ (False ∧ ((True ∨ p2) → p2))) → (True ∨ ((False ∧ (p3 ∧ (p4 → p1))) → True))) → p5) ∨ (False → (True → (p2 ∨ p3)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119479993937891266162710648912 : ((p4 → (p4 ∧ (((p3 ∨ (p3 ∨ (((((p3 ∨ p4) → (p5 ∧ (False ∨ True))) → False) ∧ (p5 ∨ p2)) → p3))) ∧ p5) ∨ p4))) ∨ (p5 ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178351433144511866675137287938 : (((p5 ∧ (p4 ∨ ((p1 ∨ (p3 ∧ (p3 → False))) ∨ p3))) ∨ (p5 → True)) ∨ (((p3 → (True ∨ False)) ∨ (p5 ∨ (True ∧ p2))) ∨ (p4 ∧ p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164983860599362656746106930113 : ((((((False ∨ True) ∨ (p1 → p4)) → ((False ∧ p3) ∨ p4)) ∧ ((True ∨ p4) ∨ False)) → p1) ∨ (True ∨ ((((False → False) ∨ p4) ∧ p2) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118626096556707463947082020547 : ((p4 ∨ (((p4 ∧ (p4 → (p4 ∨ p4))) → p1) → (((p5 ∨ True) → False) ∨ (True ∨ ((True ∧ ((p3 ∧ p5) ∧ p5)) → True))))) ∨ (True → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_758802927857080622872934305385 : (((p2 ∧ (((((True ∨ (((p1 ∨ p2) → p3) → (p3 ∧ p2))) ∧ ((((p4 ∧ False) ∨ p1) ∨ (p3 → p5)) → p2)) ∧ p4) ∧ p2) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111692668164736916794107874137 : ((((((((p2 ∧ (((p2 ∨ (p3 → p2)) ∧ p5) → (((False → p2) ∧ p5) ∨ False))) ∧ p3) ∧ p4) → False) → p4) → p1) ∨ True) ∨ (p2 ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_800132312053896809511961911859 : (((p2 → ((p5 ∧ ((p4 ∨ (p4 ∨ (((p4 → p5) ∨ (True ∧ (p1 → (True ∧ True)))) ∧ (p2 → (False ∨ (p1 ∨ p3)))))) ∨ p5)) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337548529860702759662494487291 : (p1 → ((True ∧ (((((p3 ∨ p5) ∨ ((p4 ∨ p1) → False)) ∧ p1) ∨ (p5 ∨ ((p1 → p1) ∧ p3))) ∨ False)) ∨ (False ∨ ((True ∨ p4) ∨ p3)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731807028595850971797733060263 : ((((p3 → (p5 → True)) → (((((True ∨ p5) ∨ ((p4 → ((p1 ∧ p4) → p1)) ∨ (True ∨ p5))) → (p1 ∨ p4)) ∨ False) ∨ (p1 ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_93070780621449672118625049585 : ((True ∧ ((((False ∧ p1) ∧ p3) ∨ ((p5 ∨ p5) ∨ True)) → (False ∨ ((False → (((p5 → (True ∨ p3)) ∨ p1) → True)) ∧ (False ∨ p5))))) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (((False ∧ p1) ∧ p3) ∨ ((p5 ∨ p5) ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- One of the premise coincides with the conclusion.
      exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_726180587497832196037016410275 : (((((p5 ∧ True) ∨ p2) ∨ ((p4 ∧ p1) → (((False ∧ ((p2 → False) ∨ (False → p5))) ∨ p5) ∨ (((False → p3) ∧ False) → (p4 → p1))))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_595303001805105483577084677868 : ((((((False → ((True ∨ (p5 → p4)) ∨ ((False → p3) ∨ p2))) → p1) ∧ ((p2 → ((p2 ∧ p1) ∨ p3)) ∧ ((p2 ∧ p5) ∧ p1))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262907766438846627812193875624 : (True ∧ ((True → (((p3 → (p3 → (p1 → (p5 ∨ ((p5 ∧ (True ∨ False)) → ((p3 ∨ p3) → (True ∧ p4))))))) ∨ (p1 ∧ p4)) ∧ False)) → p4)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46112249988853254209450580266 : ((((p5 ∧ ((((((p4 ∨ p2) ∨ p3) ∨ p4) ∨ p3) → ((False ∨ ((p3 ∨ True) → p4)) ∧ p4)) ∨ (p3 ∨ p5))) ∨ p4) ∧ (p2 ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40938286615088230167646503952 : (((((p3 ∧ ((p3 ∨ ((True ∧ (p2 ∨ (((p2 ∨ False) ∨ p3) ∧ (True ∨ True)))) ∨ (p1 ∧ p3))) ∧ p2)) ∨ p3) ∨ (p2 → p2)) ∨ p2) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158906060796684228793983943981 : ((p1 ∨ ((((((p1 → False) → p1) ∧ p3) ∧ (p3 ∨ p1)) ∧ p3) ∧ (p4 → (False ∧ (p3 ∧ p4))))) ∨ (((p4 ∧ p5) ∧ p3) → (p4 ∨ p2))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227320797798573766722206499980 : (((p2 → p3) → p5) ∨ (((p1 ∨ True) ∨ True) ∧ ((False → p5) → (((False ∨ p5) ∨ (p5 ∧ (p2 ∨ (p5 → (False ∧ True))))) ∨ (p4 → True))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134072477848130448300220392219 : (((((p5 → ((False ∧ ((p4 ∧ True) ∧ (((p4 → (True ∨ p5)) ∨ (p2 ∨ p4)) ∨ p1))) ∧ p5)) → p5) → False) ∨ p4) ∨ (p3 → (p3 ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204693449776477770068727316259 : (((p3 ∨ ((False ∧ p5) ∧ False)) ∨ p1) ∨ ((p1 → (False ∧ ((p3 ∧ ((p5 → p2) ∧ p1)) ∨ ((False → False) ∧ (p5 → p5))))) → (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51264086860731197301881346580 : ((((p2 ∧ p1) → (((p5 ∨ (p5 ∨ (p3 ∧ (p4 ∨ (p5 ∨ (p2 → p1)))))) → p4) → p4)) ∨ ((((p5 → p1) ∨ p5) ∨ True) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658687545443001810287801488736 : ((((p4 ∨ ((((p3 ∧ ((p4 → ((p4 ∧ True) → p2)) → p2)) ∧ p3) → (p1 ∧ p3)) → (((p3 ∨ p5) → False) ∧ p4))) ∨ (p5 ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_773828644366354586631165539492 : (((False ∨ (((((p5 ∧ True) → (p5 ∨ p2)) ∨ p2) ∧ (False → ((((True ∨ (p3 ∨ p3)) → p2) ∧ (p1 → p2)) ∨ (False ∧ p4)))) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206044432479182840966553940337 : ((p2 ∧ (p1 ∨ (False ∨ (False ∨ False)))) ∨ ((((p3 → p3) ∨ ((False → p5) ∨ (False → False))) ∧ ((p1 ∧ (False ∨ True)) ∧ p4)) → (True ∨ p2))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h3.left
      let h14 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h15 := h13.left
      let h16 := h13.right
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- False on the left can always be used.
        apply False.elim h17
      case inr h18 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h3.left
      let h21 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h22 := h20.left
      let h23 := h20.right
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h24 =>
        -- False on the left can always be used.
        apply False.elim h24
      case inr h25 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_790808034871489809292634703432 : (((p5 ∨ (p1 → (((p4 ∧ (p2 ∧ ((p5 → p3) → p2))) → p5) → (p3 ∨ (p4 ∨ (p3 ∨ ((True ∨ ((p1 → False) ∧ False)) ∨ p2))))))) ∨ p4) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_63272438750416255611499183803 : ((p5 ∧ ((p4 → ((p1 ∧ (p2 → p3)) ∧ p3)) → ((p5 ∧ ((p3 ∨ (((p3 → True) ∧ (p1 ∨ p2)) ∨ p5)) ∨ p4)) → (p3 ∨ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229377677723754556905954720381 : ((p1 → (p5 ∧ p4)) ∨ (((False ∧ ((p1 ∧ p3) ∧ (p4 → (p3 ∧ ((p3 → p3) ∧ ((p5 ∧ p3) ∧ True)))))) ∧ ((p2 → p5) ∨ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



