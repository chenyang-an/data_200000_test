variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_927284520270727755384203047834 : (((((((p1 ∨ p3) → (p4 ∨ p1)) ∧ (p3 → p2)) ∧ p1) ∧ (((p2 ∧ (p1 → False)) ∨ ((True ∧ p1) ∨ p1)) → ((p1 ∨ p3) → p3))) → p3) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h8 : ((p2 ∧ (p1 → False)) ∨ ((True ∧ p1) ∨ p1)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h9 := h3 h8
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h10 : (p1 ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h11 := h9 h10
  -- One of the premise coincides with the conclusion.
  exact h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305814064093043921001389716445 : (p1 ∨ ((p4 ∧ (True → (p3 → ((False ∧ False) → False)))) → (((False ∧ ((p3 ∧ (p2 ∧ p2)) → (p5 ∨ ((p1 ∧ p5) ∨ False)))) ∧ p3) ∨ True))) := by
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
theorem thm_5_vars_111633359479337945198073975021 : (((((((p2 → p2) → (p3 ∧ (p2 ∨ (True → p2)))) ∧ (True ∨ (p2 → True))) → (((p2 → p5) → p5) → p4)) ∨ p5) ∨ p2) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322604003995423906172897653586 : (p5 ∨ ((p2 → (p5 ∨ (((p1 → ((((((p1 ∨ p5) → (p2 → True)) ∨ True) ∨ p5) ∨ True) ∧ ((p1 ∨ p1) ∨ False))) ∧ True) → False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_105841620984546103724433609629 : (((p4 → (p4 → (((False → p3) ∧ (p2 ∧ (((p3 → False) → p1) ∧ False))) ∧ False))) → (((p2 ∧ p3) ∨ p5) ∨ (p4 → False))) ∧ (False → False)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165961333788394705049721450642 : (((False → True) ∧ (p1 → (((p5 ∨ (p2 → (False ∨ True))) → ((True ∧ p5) ∧ p3)) ∨ p4))) ∨ (p4 ∨ ((True ∧ p2) ∨ ((p5 ∧ False) → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_753885611070495630445315010015 : (((False ∧ (((p3 ∧ p5) ∨ (p4 ∧ ((p1 ∧ p4) → p5))) ∨ ((p2 ∧ (((True → True) → p2) ∨ ((p2 ∨ False) ∨ p4))) → (p1 ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40877107523934839083848510011 : ((((((p5 ∨ p1) ∨ (((False → (((p4 ∨ p4) → p3) ∨ (False ∧ True))) → False) ∨ True)) ∧ ((True ∨ p2) ∧ True)) ∧ (p1 ∨ False)) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166124172876728609944821931119 : ((True ∧ ((((((p3 ∨ (False ∨ p1)) ∧ p1) ∨ (p5 ∨ p4)) ∨ p5) ∧ p1) ∨ (False → p1))) ∨ (p3 ∨ (p4 ∧ (False ∧ ((True → p2) ∨ True))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59946729373060493554058329658 : (((True ∨ p2) → ((p4 ∧ (((True ∨ (((p3 → p3) → p2) ∧ (p4 → (True ∧ ((p2 ∧ p2) ∨ p2))))) → (p3 ∧ p2)) ∧ True)) ∨ True)) ∨ p5) := by
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
theorem thm_5_vars_150249729570179463225966714223 : ((p3 → (((((p2 → ((True → True) ∨ p1)) ∨ (p1 ∨ p4)) → (p2 ∧ True)) ∨ p1) ∧ ((True ∨ p5) ∧ True))) ∨ (p5 → ((p4 ∧ p4) → p4))) := by
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
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112588497158810674079014256341 : (((((p2 → (False ∨ (((p1 → ((p5 ∧ False) ∨ (p3 ∧ (False ∧ p2)))) ∨ False) → p3))) → (p3 ∧ p2)) ∧ (p4 ∨ p4)) → False) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_726175913131517860998472930339 : (((((p4 ∧ p5) ∨ False) ∨ (p4 ∧ ((((p5 → (p4 ∧ p1)) ∧ (p4 ∨ (False ∨ p5))) ∨ False) ∧ (p5 ∧ (p1 ∧ ((p2 → False) ∨ p5)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356765820533654684207218492189 : (p5 → ((((p4 → p3) ∨ False) ∨ (p5 → p1)) → (((p1 → ((False ∨ p3) ∨ (p4 ∧ p4))) ∨ p5) ∧ ((True ∨ (p2 ∧ True)) ∨ (p4 ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h5 =>
      -- False on the left can always be used.
      apply False.elim h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h9
  case inr h10 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_596450803765500885267199743897 : (((((p5 → ((p5 → ((p1 ∧ p4) ∧ p1)) ∧ p1)) ∨ (((p2 → p4) ∧ (p5 ∧ (p4 ∧ p2))) ∨ (True → (False ∨ (True → p2))))) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_593306175237128259546686963595 : ((((((((p3 → (False ∧ p2)) ∧ (p4 → ((p5 → p4) ∧ (p1 → ((False ∧ True) ∧ p4))))) ∨ False) ∧ p1) → ((p3 ∨ True) ∧ p2)) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112779338626158228543195847898 : (((((p3 ∨ ((p3 → (p3 ∨ p1)) ∨ False)) ∧ p5) ∨ (True → (p4 ∨ (p2 ∧ (((p4 ∧ p4) → (p5 ∧ p2)) → p1))))) → p5) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194694754394144406338499075268 : ((((p5 → p1) ∧ (p5 ∨ (True ∨ p1))) ∨ True) ∧ ((((p4 ∨ ((p3 ∨ True) → False)) ∧ (p5 ∧ (True → (p1 → False)))) ∨ p4) ∨ (p3 → True))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184820458579516342352566548621 : ((((p5 ∧ (p3 → p3)) ∨ p3) → (((False ∧ p5) ∨ p2) ∧ p1)) ∨ (((p3 ∧ p5) → (p2 ∨ p3)) → (False → ((False → False) ∧ (p4 ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156650352660029764618379466815 : ((((((p2 → (((p4 ∨ (False → p4)) ∨ (True ∨ p4)) ∨ p1)) → True) ∨ (p2 ∨ False)) → p2) ∧ p4) ∨ ((p1 ∨ p5) ∨ ((p5 ∧ p1) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_43907276666369356442730311714 : (((((p1 ∨ ((p4 ∧ ((p2 → True) → (True ∧ (p5 → ((p3 ∧ (p4 ∨ (p5 → p5))) ∨ False))))) ∨ False)) ∧ p1) ∨ (p4 → p1)) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38433482082142768576223230172 : (((((False ∨ (p4 ∨ (p2 → (p4 ∧ ((p4 ∨ p5) → True))))) ∧ (p2 ∧ p2)) ∨ (p2 ∧ (((True ∧ (p2 ∨ p3)) → False) → p3))) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133520907905125653716514630598 : ((((((True ∨ True) ∧ (p3 ∧ ((p2 ∧ False) → (((p5 ∧ p4) ∧ (p1 → p2)) ∨ (p1 ∧ p3))))) → p2) ∧ p4) ∧ False) ∨ (False ∨ (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228519949580584017396124680005 : ((p1 ∨ (False ∧ False)) ∨ (((((True → ((True ∨ (p3 ∨ (p3 ∧ p3))) → p3)) ∧ p4) ∧ (p3 → (False ∨ p2))) ∨ True) ∨ (p4 ∧ (p2 ∧ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47006715815022109094291624446 : (((((True → p2) ∨ (p3 → ((p1 ∨ False) ∨ (p1 ∨ ((p4 ∨ ((False → (p5 ∧ True)) ∨ (p2 → p4))) ∧ p2))))) → p5) ∨ (False → p1)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231319072501632192278937072794 : (((True → False) ∨ p5) → (p5 ∨ ((p4 ∨ ((p3 ∨ ((p2 ∨ False) ∨ ((False ∨ (True ∧ p3)) ∨ p4))) ∨ (p3 ∨ (p2 → (p1 ∧ p5))))) ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h4 := h2 h3
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192727745096559716983279317039 : ((((p1 ∧ False) ∧ (False → ((p5 ∨ True) ∨ p4))) → p3) → ((p4 ∨ ((p2 → p4) ∨ (p4 → p2))) ∨ (False → ((p2 ∨ p2) ∧ (p4 ∧ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325792552714806181882754557912 : (p5 ∨ (p3 ∨ ((p5 → (((p4 ∧ (False ∨ p1)) ∨ ((True ∧ (p1 ∨ True)) ∧ (p3 ∨ (((p3 → (p5 ∨ p5)) ∧ p5) ∧ p4)))) ∨ True)) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_248292691097157491029013428285 : ((p2 ∨ p2) ∨ ((True ∧ p2) → (((True ∨ ((p4 ∧ p2) ∧ ((True ∧ (p3 ∨ p2)) ∧ p1))) ∨ (p2 ∧ True)) → (p4 → (p3 ∨ (p2 ∧ p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h1.left
      let h7 := h1.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h7
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h9.left
      let h12 := h9.right
      -- Conjunctions on the left can always be decomposed.
      let h13 := h10.left
      let h14 := h10.right
      -- Conjunctions on the left can always be decomposed.
      let h15 := h13.left
      let h16 := h13.right
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h1.left
        let h19 := h1.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h17
      case inr h20 =>
        -- Conjunctions on the left can always be decomposed.
        let h21 := h1.left
        let h22 := h1.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h22
        -- One of the premise coincides with the conclusion.
        exact h22
  case inr h23 =>
    -- Conjunctions on the left can always be decomposed.
    let h24 := h23.left
    let h25 := h23.right
    -- Conjunctions on the left can always be decomposed.
    let h26 := h1.left
    let h27 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h27
    -- One of the premise coincides with the conclusion.
    exact h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166225160675288826231480472729 : ((p2 ∧ ((False → (p4 ∨ (p3 → ((True → p1) ∧ (p3 ∨ p3))))) → ((True ∨ p3) → p3))) ∨ (False → ((p1 ∨ False) ∧ (p2 ∨ (True → False))))) := by
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
theorem thm_5_vars_40189100609750479693420036979 : (((((p4 ∨ (False ∨ p1)) ∧ (p5 ∧ (((False → p3) ∨ ((p5 ∨ p2) → ((p3 → True) → p4))) → (p2 → (p1 ∨ True))))) ∧ p5) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252035387864757676568588640599 : ((p4 → p1) ∨ ((p1 ∨ ((True → p1) → (p1 → (((p4 ∧ (p5 ∧ (True ∨ (p1 → p2)))) ∨ p2) ∧ ((True → p4) ∧ p1))))) ∨ (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704363022627722443405671247409 : (((((p2 ∧ (p3 ∨ (p2 ∨ p2))) → ((p5 ∧ p2) ∧ p4)) → ((False ∧ (p1 ∨ ((p1 ∨ p1) ∧ (p3 → ((p2 ∨ p2) → p5))))) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113802351155546174469597454943 : ((((p5 ∨ p2) → (((True ∨ (p1 → (p5 → p1))) → p5) ∧ ((((p1 ∧ p4) ∧ p5) ∨ p5) ∨ (False → True)))) → (p1 ∧ True)) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2136519681768415068742541071 : ((p2 ∨ (p2 ∧ ((p4 → (False ∨ ((p3 → p4) ∨ (((p1 → p3) ∧ p1) ∧ p4)))) → p2))) → ((((p2 → p4) ∧ p2) ∨ p4) ∨ True)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255749686578736963314456835743 : ((True ∨ True) → ((((False → ((p2 ∨ p3) ∧ (p3 → p1))) ∧ (p5 ∨ p3)) ∨ False) ∨ (True ∨ ((False ∨ (p3 → (p1 → p1))) ∧ (p3 → p4))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161852952765039937103867555065 : ((True → (p3 ∧ ((False ∧ (((((p2 ∨ p1) → False) ∧ p2) ∨ (p4 ∨ p3)) ∧ (p5 → p3))) → p3))) → ((p3 → False) ∨ ((False ∨ False) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43237860869836800658224120513 : ((((p3 ∨ (((((p3 ∨ False) ∨ True) → (p4 ∨ ((True ∨ True) ∧ p4))) ∧ p1) ∧ (((p2 ∨ (True → p1)) → False) ∨ p2))) ∧ p4) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61214513741090613955694919738 : ((False ∧ (True ∧ ((p4 → (((p3 → p5) ∧ (((True ∧ (p5 ∧ (True → True))) ∨ p2) ∨ p2)) → p5)) ∨ (((True ∧ p1) ∧ False) ∧ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_628837167543056811804072336764 : (((((p4 → ((((False ∧ True) ∨ True) → False) ∧ ((((True → False) ∨ p5) ∨ ((((p3 → p1) ∨ p4) → False) → True)) ∨ p1))) ∧ p1) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337434757041727879357828383416 : (p1 → ((((p4 → ((False → (False ∧ (p2 ∧ p1))) ∧ p5)) ∧ True) → ((p5 ∨ ((p2 → (p1 ∨ p1)) → p5)) → p3)) → ((p2 → p2) ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51666224656148202535063701289 : (((((p5 ∨ True) ∧ (((p1 → (p3 ∧ (False ∨ p5))) ∧ (p2 ∨ p4)) ∨ p5)) → False) ∧ ((p5 ∧ (p1 ∧ ((p5 ∧ p1) → False))) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118783143942537338321942233923 : ((p5 ∨ (p4 ∨ (((p3 ∧ ((p1 → p1) → (p3 ∧ p1))) ∧ p1) ∨ (p4 ∧ (((p2 → (p1 ∨ p1)) ∨ (p2 ∨ p3)) → p4))))) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_427999114965721131437004856505 : (((((p4 ∧ ((p4 ∨ (((p3 ∧ (p5 ∨ (p3 ∨ True))) → p1) ∧ (((p5 → False) ∨ p1) → p5))) → (p5 ∧ p3))) ∨ p2) ∨ (p1 → True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_321620342196170012249162925972 : (p4 ∨ (p3 → (((((p5 ∧ p4) ∨ p4) ∧ ((p2 ∨ True) ∧ p2)) ∨ p5) → ((((True → p4) ∧ p3) ∧ (((p1 ∧ p5) ∧ p2) ∨ p4)) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h5.left
      let h10 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h5.left
      let h15 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
  case inr h18 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300538583766671952545131636615 : (False ∨ (((p3 ∧ ((p4 ∧ (p5 ∧ True)) ∨ ((p5 ∨ p3) ∨ ((p5 ∧ False) ∨ ((p5 → p1) → p2))))) ∨ p5) ∨ ((p4 → (p3 ∨ True)) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_67981412213503202999355042916 : ((p2 → ((False ∧ False) ∧ (((p2 ∧ (((p1 ∨ p4) ∧ (p4 → p4)) ∧ p4)) ∧ ((True ∨ p5) → p2)) → (((p3 ∨ p1) ∨ p1) ∨ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683872570601859445073888026175 : (((((p5 ∧ ((p4 ∨ False) → ((p4 ∨ p1) → (p2 ∨ (p3 ∨ ((p2 ∧ p3) ∧ p5)))))) ∨ False) ∨ (True ∨ ((True ∨ False) ∨ (p3 → True)))) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_618988453017888529444714918128 : ((((((p2 ∧ p3) ∨ p3) ∨ (p2 ∧ (p4 ∧ (((((False → p1) ∨ p1) ∨ ((p1 ∧ p4) ∨ True)) ∧ p5) ∧ (p4 → (False ∨ True)))))) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_159717814898880144598986347861 : ((((True ∨ (((p5 ∨ (p3 → False)) ∨ p3) → (p4 ∧ p3))) ∨ (((p3 → p2) ∨ p5) ∧ p4)) ∨ p2) → (p2 → ((p1 ∨ p3) ∨ (p2 ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h2
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
        exact h2
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h2
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40341953152210258767510668635 : (((((False ∧ ((p2 ∨ p1) ∨ ((p1 ∨ True) → (((True → True) ∧ (((p4 ∨ p3) → (True → p5)) → p2)) → p5)))) ∨ True) ∨ p3) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135929900006559991794843421866 : (((p3 → (((((p5 ∨ (False → p3)) ∨ False) ∨ p5) ∧ p5) ∨ p1)) → (p3 → ((p4 → False) → (p2 → (p2 ∧ False))))) ∨ (p2 ∨ (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111452616771826976968996790115 : (((True → ((True ∧ p2) ∨ ((False ∨ p5) → (((True ∨ (p3 ∧ p1)) ∧ p4) ∧ ((p4 ∧ (p4 ∨ (p2 ∨ False))) ∧ p4))))) ∧ p5) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63953008270559846931300723242 : ((False ∨ ((False ∨ (((p5 ∨ p1) → ((p1 → (p4 → False)) → (False ∨ False))) ∨ ((False ∨ p4) ∨ (True → (True ∨ (True ∧ p1)))))) ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148673821891923395532366698821 : ((((p2 ∨ (p4 ∨ ((p5 ∨ p1) → p1))) ∨ p2) ∨ ((True ∧ ((p5 ∨ (p5 → p4)) ∨ p1)) → (p5 ∨ True))) ∨ (((p4 ∨ False) ∨ p4) → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
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
theorem thm_5_vars_342397372672560643244347583728 : (p2 → (((p3 ∧ p5) ∨ ((p5 → (p1 ∨ ((p1 ∧ p3) ∨ True))) → (p4 ∧ (p3 ∧ p2)))) ∨ (p2 ∧ (((False ∧ (p2 → p1)) ∨ p4) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_922333242924585118172657599012 : ((((((False ∧ p5) → p2) → ((((False ∧ (True ∨ p1)) ∧ p1) → False) ∨ p4)) → ((((p2 → p3) → (p1 → p2)) ∨ p2) ∧ (p2 ∧ False))) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((False ∧ p5) → p2) → ((((False ∧ (True ∨ p1)) ∧ p1) → False) ∨ p4)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h2
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- False on the left can always be used.
  apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47994242542782394762316212989 : ((((p5 ∨ (((((((p1 ∧ p1) → p3) → p5) ∨ p2) → p3) ∨ p1) ∧ p1)) ∧ ((False ∧ (p5 ∧ (True ∧ False))) ∨ p3)) → (p3 → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165001010252068492662928708707 : (((((p5 ∧ ((p3 ∨ p5) ∧ (p1 ∧ True))) ∧ False) → ((False ∨ p5) ∧ (p5 ∨ True))) → p2) ∨ ((True → True) ∧ (p1 → (p1 ∨ (p5 ∨ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_98815502258828492427469326389 : ((True → ((((True ∧ (p1 ∨ True)) ∨ p2) ∨ ((p5 ∧ (((((p3 ∨ p3) ∨ p4) ∨ (p4 ∧ (p2 ∨ True))) ∨ p1) ∨ p1)) ∨ p2)) ∧ p3)) → p3) := by
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
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63990595555359431127202066159 : ((False ∨ ((p4 ∧ ((((p1 ∧ (True ∨ ((p2 → (p1 ∧ (p5 ∧ (False ∧ False)))) ∨ p1))) → (p4 ∧ (p2 → p3))) ∨ p5) ∨ False)) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_89289030503116455610678374172 : (((True ∨ (True → p2)) ∧ ((p2 ∧ (p2 ∨ ((((p1 ∨ p2) ∨ False) ∧ (p1 ∧ ((p1 ∧ True) ∨ (p3 ∨ p4)))) → p4))) ∧ (p1 → p4))) → p2) := by
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
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h3.left
    let h13 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h12.left
    let h15 := h12.right
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- One of the premise coincides with the conclusion.
      exact h16
    case inr h17 =>
      -- One of the premise coincides with the conclusion.
      exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52626130219132664295562192917 : ((((p4 ∨ (p1 ∧ True)) → (p2 ∧ ((((p3 ∨ p3) ∨ p3) → False) ∨ p3))) ∨ ((((False ∨ False) ∧ (p2 ∨ p1)) → (p2 → p5)) ∧ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66562210001977435419334896288 : ((True → ((((p4 → (False ∧ (p3 ∨ (p1 → p3)))) → ((((True → False) ∨ (p5 → p5)) ∨ p4) ∨ (p2 → p2))) ∨ p2) ∨ (p4 → p5))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166472005974193071024813103294 : ((p3 ∨ (((p5 ∨ (False ∨ (((p5 ∧ p2) → True) ∧ p2))) ∧ ((False ∧ p4) ∨ p4)) ∧ p5)) ∨ ((p4 → ((p1 ∨ p4) → (p5 → p4))) ∨ p4)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302823174437626584383695061140 : (False ∨ (p5 ∨ ((((True → ((p4 ∧ True) ∨ True)) → ((p4 ∧ False) ∨ p4)) ∧ p2) → (((p4 ∧ False) ∨ ((p3 → False) → (p1 ∨ p2))) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208147159639062532105254260808 : ((((p3 ∨ p3) → False) → (p2 ∧ p2)) → (((p4 ∨ True) → (((p2 ∨ (p1 → p2)) ∧ (((p1 → p2) ∧ False) → True)) ∧ p3)) → (p5 ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p4 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137976000862328502259544659749 : ((p5 ∨ ((((True ∧ (p3 → p1)) ∧ p2) ∧ True) ∨ ((p3 ∨ p5) ∨ ((True → False) → ((True ∧ p2) → (p5 ∧ p5)))))) ∨ (p5 ∧ (p4 ∧ p2))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h2.left
  let h8 := h2.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h9 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h9
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135187066214597106491365406262 : ((((((p4 → (p1 → (p4 ∧ p3))) ∨ (p5 → (p5 ∨ ((False ∧ (p2 ∨ True)) ∧ p2)))) ∨ p5) → p1) → (False ∧ p3)) ∨ ((True ∨ p3) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233300989892540438631460026973 : ((True ∨ (p3 ∨ p2)) → (((((p4 ∨ (True ∧ p4)) ∨ ((p3 → p3) → ((p4 ∧ False) ∨ (True ∨ p2)))) ∨ (False ∧ (p1 → p4))) ∨ p5) ∨ True)) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_782384707639685608893118380774 : (((p3 ∨ (((((False → ((((p5 → p4) ∧ (p4 ∧ p3)) ∧ p3) → (p5 ∨ False))) ∧ (p1 ∨ (True ∨ (False → True)))) ∧ p2) → p3) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37411869153276081517845557490 : (((((False ∨ (((p1 ∧ p4) ∧ (((p2 ∨ ((True → p1) → (p4 ∧ (True ∨ p5)))) → p3) ∧ p4)) ∨ p4)) ∨ (True ∨ p3)) ∨ p4) ∧ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_134236466730050874834375983221 : (((((p4 ∧ (p1 ∨ p5)) ∨ p1) ∨ ((p1 ∨ (p5 ∧ p2)) ∧ (False ∧ ((p3 → ((p3 ∨ p3) → p1)) → p3)))) ∨ p4) ∨ (True ∨ (p4 ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47009016079257657079911651759 : (((((p1 → p4) → (True ∨ ((((((p2 → p5) ∧ ((p4 → False) → True)) → p5) ∨ p4) ∧ (p5 → True)) → True))) → p3) ∨ (True ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185391312292826113901034889540 : ((p5 ∧ (p3 ∨ ((p2 ∧ True) → ((p1 ∨ p5) ∧ (p5 → p3))))) ∨ ((p1 → (p4 → (p4 → ((((p2 ∧ p4) ∨ False) → p2) ∧ True)))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327850716929577934768168050309 : (True → (((p1 ∧ (p3 → (((p2 ∨ p2) ∧ p1) ∧ p2))) → ((True ∧ ((p4 → (p3 ∧ True)) → ((p1 ∧ p1) → p1))) → p4)) ∨ (p2 → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68712601254589654437066003012 : ((p4 → (((p1 → p4) → ((p4 ∧ ((p1 ∨ (p3 ∧ ((p3 ∨ True) ∨ p4))) → (p4 ∨ p3))) → (p1 ∧ p1))) ∧ (p2 ∧ (p5 → p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_716043823582832123770802970643 : ((((((p1 ∧ p3) ∨ p2) → True) ∧ (((p5 ∨ True) ∨ p5) ∧ ((p1 ∧ p1) ∨ (((p4 ∧ ((False → (p4 ∨ False)) ∨ p3)) ∧ p4) ∨ True)))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47637819051167380085757609994 : (((((((p3 ∨ (p1 ∨ False)) ∨ False) → (False → (p4 → ((True → (p3 ∨ p5)) → ((p5 ∨ p5) ∨ p2))))) ∨ p5) ∧ p1) → (True → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197409396100985257454444568424 : (((p1 → ((p1 ∧ False) ∧ (p4 → p5))) → p1) ∨ (((((False → True) → ((p3 → ((p4 ∧ p3) → p1)) ∨ p2)) ∨ False) → p3) ∨ (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258253325233525893303673947698 : ((p4 ∨ p5) → ((p5 ∨ p1) → ((p3 ∧ (p2 ∧ p1)) ∨ ((p4 ∧ ((p4 → (p2 → p2)) → ((False ∧ p2) → (p1 → (p4 ∨ False))))) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h4 =>
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
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164577518158776295185086710810 : (((((False ∧ p2) ∨ False) → (p2 ∨ (((True → p3) ∨ p1) ∧ (True ∨ (True ∧ p2))))) ∧ p5) ∨ ((p2 ∨ p3) → (((p1 ∨ False) ∧ p4) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_676440978860963873589226652857 : (((((p3 ∧ p2) → (p2 → (((p5 → p5) → (p2 → p3)) → (((p3 ∧ p1) ∧ p5) ∨ (p3 → p1))))) ∧ ((p3 → (p5 → p4)) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40102428666384873503177543675 : (((((((p2 ∧ (False ∧ (False ∨ (p5 ∨ True)))) ∧ p1) ∨ (p1 ∨ (p4 → ((p3 ∨ (p5 → p3)) ∧ p4)))) ∧ (True ∧ p2)) ∧ p3) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158235465380881024877983216513 : (((p4 → (p2 ∧ True)) ∧ (p2 ∧ (p2 ∧ (p4 ∧ ((p5 ∧ ((p2 ∨ (p4 → p1)) ∨ p2)) → p4))))) ∨ ((True ∧ (p1 → p3)) → (p1 ∨ True))) := by
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
theorem thm_5_vars_308515211608050246171843936971 : (p2 ∨ (((((p2 → (p1 ∧ ((p2 ∨ (True → p4)) → False))) → (p3 ∧ p2)) ∨ (True ∨ p2)) ∨ (((p1 → p1) → p2) ∨ (p1 ∨ p1))) ∨ p1)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40719264387752239649218736045 : ((((((False → (p2 → p4)) ∧ ((p2 ∧ False) ∨ p4)) → (True → (((p2 ∨ ((p4 ∧ (p4 → p1)) ∨ False)) → p5) ∨ p1))) → p5) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201096543697805282991298699403 : ((True → ((p5 ∨ ((p2 ∧ p2) → p2)) ∧ p1)) → ((((((p5 ∨ ((p1 ∨ p4) ∨ p5)) → False) ∧ p1) → p5) → p3) → ((p3 ∨ p4) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_823882539597604706018865306962 : (((((p5 → ((False ∨ False) ∧ p3)) ∧ ((((p2 ∧ (((p5 → (p3 ∧ ((p5 ∨ True) ∨ True))) ∧ p5) ∨ False)) → p1) ∨ p3) ∨ p3)) ∧ p5) → False) ∧ True) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h8 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h9 := h4 h8
      -- We need to get the left conjuct of h9 based on <expert-advice>.
      let h10 := h9.left
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- False on the left can always be used.
        apply False.elim h11
      case inr h12 =>
        -- False on the left can always be used.
        apply False.elim h12
    case inr h13 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h14 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h15 := h4 h14
      -- We need to get the left conjuct of h15 based on <expert-advice>.
      let h16 := h15.left
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- False on the left can always be used.
        apply False.elim h17
      case inr h18 =>
        -- False on the left can always be used.
        apply False.elim h18
  case inr h19 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h20 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h21 := h4 h20
    -- We need to get the left conjuct of h21 based on <expert-advice>.
    let h22 := h21.left
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h23 =>
      -- False on the left can always be used.
      apply False.elim h23
    case inr h24 =>
      -- False on the left can always be used.
      apply False.elim h24
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355886526132171293898019156608 : (p5 → ((p4 ∨ (((((p3 ∧ (p2 ∨ p2)) → (p4 → p4)) ∨ p1) → ((p4 ∨ (p1 ∧ True)) ∨ (p3 ∨ True))) ∨ p5)) ∨ ((p5 → p5) → True))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53842991354817740799956231533 : ((((p1 → ((p3 ∨ p4) ∧ False)) ∨ ((p4 ∧ p5) ∨ True)) ∨ (p1 → (((p5 ∧ p4) ∨ p4) ∨ (((p3 → p5) ∨ (p2 ∨ p2)) → True)))) ∨ p1) := by
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
theorem thm_5_vars_158194094819498971972181325823 : ((((p2 ∧ p2) ∧ True) ∧ ((((p2 → False) ∧ p1) ∨ p5) ∨ ((True ∨ ((True ∨ True) ∧ True)) ∨ p1))) ∨ (p2 → ((p2 → (False ∧ p4)) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42033111189115357654663520420 : ((((p3 ∧ p2) ∨ ((p3 ∧ ((p5 → False) ∧ p5)) → ((p4 → ((p1 ∨ ((p5 ∧ True) ∧ p4)) → ((p1 ∧ False) ∧ True))) ∨ p3))) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309923815768164007120415188621 : (p2 ∨ ((((p1 ∧ p1) ∨ (((True → (p1 ∧ p5)) ∧ p4) ∨ p4)) ∧ ((True ∧ (p1 ∧ False)) ∧ p5)) ∨ (p5 ∨ (p4 → ((p4 ∧ True) ∨ p3))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161621282877969612852608318876 : ((False ∨ ((False ∨ ((p3 ∨ p2) ∧ p5)) → (p4 ∧ (((((False ∧ False) ∨ p3) → p1) ∨ False) ∧ p1)))) → (((p2 ∧ (p3 ∧ p4)) ∨ True) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316867902559222271985410853369 : (p3 ∨ (p1 → ((p4 → (((p3 ∨ p5) ∨ True) ∧ (p4 → (((p2 ∨ (p2 ∨ ((p3 ∨ p1) ∧ p3))) ∧ p1) ∧ True)))) ∨ (p1 ∨ (True → p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218765511726720538911094764660 : ((p1 ∧ ((p5 → p4) ∧ True)) → ((p5 ∨ (p4 ∧ (((p3 ∨ True) → False) ∧ (False → (p1 → p5))))) ∨ (((p5 ∧ p1) ∧ p2) ∨ (p4 ∨ p1)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299492925503745001483316051463 : (False ∨ ((p3 → ((p4 ∧ (p5 ∨ True)) → (((p2 ∨ ((p2 ∨ True) ∧ p1)) ∨ (p1 ∨ p2)) ∧ (p5 ∧ ((p3 ∧ False) → (p5 ∧ p4)))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350504864789983692800428641146 : (p4 → ((((True → ((p1 ∧ p3) ∨ ((p1 ∧ True) ∨ (p5 → (p4 ∨ p5))))) ∧ (p4 ∧ ((p5 ∨ True) ∨ (p4 → p1)))) → (False ∧ p2)) → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((True → ((p1 ∧ p3) ∨ ((p1 ∧ True) ∨ (p5 → (p4 ∨ p5))))) ∧ (p4 ∧ ((p5 ∨ True) ∨ (p4 → p1)))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h1
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h3
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60442985618883117621545864263 : (((p5 → True) → (((((p1 ∧ p3) ∨ (False ∧ (p5 ∧ (p1 ∧ True)))) ∨ p5) ∧ ((True ∨ p2) → p5)) ∨ (((p1 → p5) ∨ p2) → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



