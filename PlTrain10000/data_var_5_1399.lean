variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330901778336585214251639558865 : (True → (p4 → ((((((False ∨ p5) ∨ (p2 ∧ p2)) ∨ p5) ∧ (p2 ∨ ((((p5 ∨ p1) → (p5 ∧ p3)) ∨ (p2 ∧ p5)) ∨ p4))) ∧ p3) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192080857317203380399507021457 : ((p3 → (p1 → (p2 ∨ (p4 ∨ (p4 ∧ (p2 ∨ p3)))))) ∨ ((p4 ∨ (((((p5 ∨ p5) → p2) → p1) → ((True ∧ p1) → True)) ∨ p1)) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174306906834510511106538783205 : (((((p2 ∧ p5) ∨ (p1 ∧ (False ∧ False))) ∨ (False → p4)) ∨ (p5 → (p1 ∨ p3))) → (((p4 ∧ ((p1 ∧ (p2 ∨ p1)) ∧ True)) ∨ True) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h4 =>
        -- Conjunctions on the left can always be decomposed.
        let h5 := h4.left
        let h6 := h4.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- False on the left can always be used.
        apply False.elim h10
    case inr h12 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h13 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68831424127291033487791158234 : ((p4 → ((True ∧ p4) ∧ (True ∧ ((p1 → (p1 ∧ ((p4 ∧ (p5 ∨ (False → ((p4 → ((p5 ∧ p4) ∧ p3)) → p5)))) ∨ p2))) → p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113886123834022300376185828792 : (((((((p5 ∧ ((True ∨ p3) ∨ (p5 ∨ ((p4 ∨ p3) ∨ p4)))) ∧ p4) → False) ∧ (p5 ∨ p4)) ∨ p1) ∧ (True → (p2 → True))) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349235510435282873818290216086 : (p3 → (p1 → (((p2 ∨ (p1 ∧ (((False ∨ False) → True) ∨ (p4 ∨ p5)))) → p4) ∨ (p2 → (((p3 ∧ (p1 ∧ (p5 ∨ p5))) ∨ p5) → p2))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h11 =>
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h12 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174106751466474654441771845198 : ((((p4 ∧ p3) → ((((p2 ∨ p4) ∨ (True ∧ True)) ∨ True) → True)) ∧ (p5 → p1)) → (((p5 ∧ p1) ∨ (p5 ∨ (False ∨ (False → False)))) ∨ True)) := by
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
theorem thm_5_vars_248652740548269120572742388898 : ((p3 ∨ p1) ∨ ((p1 ∨ (False ∧ False)) ∨ (False → ((((p2 ∨ (p4 ∧ p3)) ∧ (p5 ∧ (True → p2))) ∧ p2) → (p4 ∧ ((False → p2) ∧ False)))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- False on the left can always be used.
    apply False.elim h1
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h6.left
    let h14 := h6.right
    -- False on the left can always be used.
    apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h15
  -- False on the left can always be used.
  apply False.elim h15
  -- Conjunctions on the left can always be decomposed.
  let h16 := h2.left
  let h17 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h18 := h16.left
  let h19 := h16.right
  -- Disjunctions on the left can always be decomposed.
  cases h18
  case inl h20 =>
    -- Conjunctions on the left can always be decomposed.
    let h21 := h19.left
    let h22 := h19.right
    -- False on the left can always be used.
    apply False.elim h1
  case inr h23 =>
    -- Conjunctions on the left can always be decomposed.
    let h24 := h23.left
    let h25 := h23.right
    -- Conjunctions on the left can always be decomposed.
    let h26 := h19.left
    let h27 := h19.right
    -- False on the left can always be used.
    apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_485259062706092090008739381207 : ((((((p2 ∧ (p5 ∨ p3)) → p3) ∧ p4) ∨ ((p2 ∧ (p3 ∧ p2)) ∨ (p4 ∨ (p5 → (((p5 → (False ∧ p2)) ∧ p5) ∨ (p5 ∨ p5)))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_592530334402278074244928128258 : ((((((p1 ∨ True) → ((((p4 → False) ∧ (((True ∨ p5) ∨ p1) → (False ∧ True))) ∧ (p4 → (p3 ∨ p1))) ∧ p5)) → (p3 ∧ p3)) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56083331870705307838874173494 : ((((p1 → (p4 ∧ p4)) → p4) ∨ (((p2 ∨ p2) → ((False ∧ (p1 ∨ ((p2 → p4) ∧ p5))) → (p4 ∧ p2))) → (p1 ∨ (p5 ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257111055804997214097455635779 : ((p2 ∨ False) → (p5 ∨ (True ∧ ((((p4 ∧ (p4 ∧ p3)) ∨ (((p2 ∧ True) → p1) ∧ True)) ∧ (((p4 ∧ p3) ∨ (False → p3)) ∧ False)) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337757073009167723106894367230 : (p1 → (((((False → (p5 → (p2 ∨ p1))) ∧ (p1 ∨ ((False ∨ p3) → p4))) → False) ∨ p1) ∨ ((((p2 ∧ (p4 → p1)) ∧ p3) ∧ p4) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199569948551941194516874262682 : (((((p5 ∨ p3) ∨ (False ∧ p1)) ∨ True) → p3) → (p4 → (((p3 ∧ ((p5 ∧ p1) ∨ (True ∧ p3))) → (p3 ∨ ((False ∧ p1) ∧ False))) ∧ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h11
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h12 : (((p5 ∨ p3) ∨ (False ∧ p1)) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h13 := h1 h12
  -- One of the premise coincides with the conclusion.
  exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_639340500995867727707627622989 : ((((((p3 ∧ p1) ∨ (p3 → p1)) → ((False ∧ (p2 ∨ (p1 ∨ ((False ∧ p1) ∨ True)))) ∨ ((p1 ∧ (p5 → (True ∧ p3))) ∨ False))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312291021196823694570472373208 : (p2 ∨ (p2 → (((((p4 ∧ False) → p1) ∧ p1) ∧ ((p5 ∨ ((p5 → p5) → (((True ∧ (True → (p2 ∨ True))) → p5) → p4))) ∨ p4)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147071560339912587000126843296 : ((((False ∧ (((p5 → p5) ∧ False) ∨ p2)) ∧ (p4 → ((p3 ∧ (True ∨ (True ∧ (p2 → True)))) ∨ p2))) ∧ p3) ∨ (True ∨ (p4 → (p4 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62008429237299913423276195562 : ((p2 ∧ (((False → p3) ∨ (p1 ∧ True)) → ((True → (p2 → p5)) → ((p2 → (((p4 ∧ p3) → p5) ∨ (p1 → p4))) ∧ (p3 → p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115071288749956488757488071258 : ((((p2 ∧ p4) ∧ (p2 ∧ (True → (((p1 ∧ p4) → p2) → True)))) ∨ (((p2 ∧ (p5 ∨ p2)) ∧ p4) ∨ (p4 ∧ (p5 ∧ False)))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313958596264049499946247874009 : (p3 ∨ (((((((False ∨ p2) ∨ (p3 ∧ p4)) ∨ p4) ∨ ((p2 ∨ (p5 ∨ p4)) → (p1 → (p3 ∨ p2)))) → p3) → (p2 → p1)) ∨ (True ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158537561455873104658398152760 : (((p1 → p2) → ((p5 ∧ (p4 → p3)) ∨ (False ∧ (p5 ∧ (True ∨ (p4 ∨ (True ∨ (p3 ∨ True)))))))) ∨ (p4 → (p3 → ((p3 ∨ p2) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4665369556553949263227013281 : (p5 → ((p2 ∨ p3) ∨ ((p3 ∧ (((True ∨ ((p4 ∨ False) ∧ False)) → (p2 ∧ ((p5 ∨ p3) ∨ False))) ∧ p3)) ∨ (p2 → (p5 ∧ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110986336905036372406945915901 : (((((p1 → False) → (((p4 ∨ (p3 ∧ False)) ∨ (p5 ∨ p4)) ∧ (p5 ∨ (False ∧ ((p5 → p5) → p4))))) → (p2 → p5)) ∧ False) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_716833620079119537473094295638 : ((((False ∧ (p2 → (p2 → p5))) ∧ (((p5 → (False ∧ False)) → False) ∨ (((True ∨ (p5 ∨ True)) ∧ ((p3 ∧ (p2 ∨ False)) ∧ p5)) ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112747652199488098719304236000 : (((((((True → (p3 → p4)) → p3) ∨ ((p3 ∨ False) ∧ p2)) → False) → (p1 → (p3 → (p5 ∧ ((p5 ∨ p1) ∨ p1))))) → False) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69030605895632386703367266568 : ((p5 → ((((((p5 ∧ ((p2 ∧ p5) → True)) ∨ True) → (p4 → p3)) ∧ (p2 ∨ (((True ∧ p5) ∨ False) → (p1 → p1)))) → p1) ∨ p5)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178815194263870117147044833830 : (((p5 ∧ (p5 ∨ p2)) ∨ (True ∧ ((p1 → p1) → (False ∧ (p2 ∨ p4))))) ∨ (False → (((True → (p5 ∨ ((p5 → False) → p2))) ∧ p4) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198108996336355614635220909590 : (((p3 → False) ∨ (p1 ∧ ((False ∧ p3) → p1))) ∨ (((p3 ∨ p1) ∨ (((((False ∨ p1) ∨ (p4 → True)) ∨ True) ∨ p1) → p2)) → (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
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
theorem thm_5_vars_757095076678748735047448274912 : (((p1 ∧ ((p3 ∨ (True ∧ p5)) ∧ (p1 → ((p5 → p4) ∨ ((True ∨ (p1 ∧ (p1 ∧ p2))) ∧ (p2 ∧ (p3 → ((p5 ∧ p1) ∨ p5)))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148487358613296631709094523439 : ((((False → ((p4 ∧ (True ∧ p5)) → (p1 ∨ (p3 ∧ p2)))) → p2) ∨ (((p3 → False) → (False ∨ True)) ∨ p3)) ∨ (p3 → (p2 ∨ (True ∨ p5)))) := by
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
theorem thm_5_vars_262463990651239764353614617879 : (True ∧ ((p2 ∨ ((True → False) → ((False ∧ ((p2 → (p1 → ((p4 ∧ p1) ∨ False))) → (p4 ∧ p2))) ∨ (False → ((p1 ∧ p2) ∨ True))))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58522593671002276109693686322 : (((p5 ∨ False) ∧ (p5 ∨ ((p2 ∧ p2) ∨ ((p3 ∨ ((True ∨ p3) → (p2 ∨ (p1 ∨ (((p4 ∨ p2) → True) ∧ (True ∨ p2)))))) ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147467397012890741640321547358 : (((False ∧ (((p2 ∨ (p3 ∧ (((p3 ∨ p2) → True) ∨ ((p5 → False) ∨ p1)))) ∨ p2) ∨ (p4 ∨ False))) ∨ True) ∨ (p3 ∧ (True ∧ (True ∨ p5)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180456147846825035902436671151 : (((True ∧ (((p4 → p5) ∧ p5) → ((p3 → p2) ∨ False))) → (p2 ∨ p3)) → ((False ∨ (p5 → p2)) → ((p2 ∧ p2) ∨ (p3 → (p1 ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303227034332541430801187269393 : (False ∨ (p5 → ((((p2 → (False ∨ False)) ∨ (p1 ∧ p2)) ∨ (False → (p4 ∨ (((False ∨ (p1 → ((True ∨ p1) ∧ p1))) → p4) ∨ p4)))) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354070330220009557605998671243 : (p4 → (p4 → (p4 → ((((p4 ∨ (p4 ∨ (p4 ∧ p3))) ∧ (p3 → (True ∧ (((p5 ∧ True) ∨ p2) → (p1 → (False ∧ p1)))))) → p2) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319510140044238282188044393741 : (p4 ∨ (((((p3 → (True → p1)) → (p1 ∨ True)) ∧ p5) → True) ∧ (p1 → (((p3 ∧ True) ∧ ((p3 ∨ p5) → ((False ∨ True) ∧ p3))) ∨ True)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327116782612132503194704008016 : (True → (((p1 ∧ p3) → ((((p2 ∨ False) ∨ ((True → (p1 ∧ (p4 ∨ p1))) ∨ p2)) → p4) ∨ ((p1 ∨ p3) ∧ (p1 → (True → True))))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326953349697142151754816247153 : (True → ((((((True ∧ p4) → True) ∨ ((p5 ∧ False) ∨ (p4 ∨ ((p3 → p4) → True)))) → (p5 ∧ (False ∧ (p4 ∧ p1)))) ∨ (p5 ∨ p1)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64724867570694827960034909590 : ((p1 ∨ (p4 → (p5 ∨ (((p5 → (((((p4 ∨ (p2 ∧ p1)) → p4) ∨ p2) ∧ ((p4 → p2) → p4)) ∧ False)) → p5) ∨ (False → p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336298121466397012013006639691 : (p1 → (((((True ∨ p3) → p2) ∨ (p1 → p5)) ∧ (p4 ∧ ((True → (p3 → True)) → ((p2 ∨ (p3 ∧ ((True → True) → p4))) ∨ p4)))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_266155865070219931596119430818 : (True ∧ (p3 → ((True → p2) → (p4 → (p2 ∧ ((((((((True → False) → p5) ∧ (False ∧ False)) ∨ p5) → (True → p3)) → p5) ∧ p2) ∨ p3)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207558900250963189606135072325 : (((((False → True) ∨ True) ∨ p1) → False) → ((((p1 ∧ (p5 ∨ ((p3 ∧ False) → p4))) → p5) ∧ p2) ∨ (p3 → ((p1 ∨ (p3 ∧ p4)) → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((False → True) ∨ True) ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326620184819735453324823365822 : (True → ((((False ∨ (p1 ∨ (p2 → False))) ∧ (p4 → p5)) ∨ ((p2 ∧ (p3 ∨ p1)) ∨ (True ∧ ((p5 → p4) → (p1 → (p3 ∨ p1)))))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171416453084837521862246411618 : (((((p4 → p4) ∧ p3) → (p4 ∨ ((p2 ∧ ((p5 ∨ p5) → p4)) ∧ False))) ∧ True) ∨ (p5 ∨ ((p3 ∨ (False → p2)) ∨ (p5 → (p4 ∧ p4))))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200576657135170624242496315964 : ((True ∧ ((True ∧ (p5 ∨ (p3 ∧ p1))) ∨ p1)) → (((p2 ∨ p3) → False) ∨ (p5 → (True ∧ ((p1 ∨ ((True ∨ (p3 → True)) → p3)) ∨ True))))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h14
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323990552685225242859068685024 : (p5 ∨ (((True → (((((p1 → p3) ∨ True) ∨ False) ∧ p5) ∨ p1)) → (p2 ∧ p4)) ∨ (False ∨ ((True ∨ (p3 → True)) ∨ ((p3 → True) → p1))))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_775280748071725567805262363227 : (((False ∨ (True ∧ (((True ∧ (p2 → (p4 ∨ p3))) → ((((False ∨ (p5 ∧ p2)) ∨ (p4 ∨ p2)) ∨ (False ∨ (p3 → True))) ∨ p2)) ∧ True))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241633703774560711384247526350 : ((False → p5) ∧ (((p3 ∨ ((True ∧ (p2 ∨ (p3 → (p5 ∨ p4)))) ∨ True)) → ((((True ∨ False) ∨ True) ∧ (p1 ∧ p5)) ∨ (p3 → p3))) ∧ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h10
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h12
        -- One of the premise coincides with the conclusion.
        exact h12
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- One of the premise coincides with the conclusion.
      exact h14
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117319696823230552814927248177 : ((False ∧ ((True ∧ ((p1 ∨ p4) → ((p2 ∧ (True ∧ True)) → p3))) ∧ (((p2 → (p5 ∨ p3)) ∨ ((True ∧ p2) ∨ p3)) → p4))) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157318226006992771177317952280 : (((p3 ∧ (p4 ∨ (((p3 ∨ (p1 → (((p4 → (False → p4)) ∧ True) ∧ p2))) ∨ p3) ∨ False))) → p4) ∨ ((p4 ∨ (p2 ∧ p1)) → (True ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37963457091426115697668785789 : (((((p5 ∨ ((p4 → ((False ∧ (((p3 → False) → p2) → True)) ∨ p3)) ∧ (p4 ∧ (p5 ∧ (False ∧ p4))))) ∨ False) ∨ (p3 → False)) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_660344018190011530034523075723 : (((((p1 ∨ (((p3 ∨ (False ∧ p4)) ∨ ((p4 → (p2 → (p2 ∧ p3))) ∧ (p4 → False))) → (p5 ∧ (False ∧ False)))) ∨ p5) → (False ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51927767094193450405439469872 : ((((((p5 ∧ (p4 ∨ True)) ∧ p2) ∨ ((True ∧ p2) ∧ False)) ∨ ((True ∧ p1) → True)) ∨ (p5 ∨ ((p5 ∨ ((False ∧ p2) → p4)) ∧ p2))) ∨ False) := by
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
theorem thm_5_vars_615366074053215892595059590586 : (((((((p2 → (p1 ∧ p5)) → p3) → (((True → p5) ∨ p3) ∨ ((p4 → p4) ∧ p4))) ∨ (p2 → ((False → (p1 ∨ p4)) → False))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121591544961733714965532230410 : (((((p5 ∨ (p2 ∨ (p3 ∧ ((p2 ∧ p3) ∧ p3)))) ∧ (((p2 ∨ p3) → (p3 ∨ p3)) ∨ p5)) ∨ ((p2 ∧ p1) → p1)) → False) → (p3 ∧ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p5 ∨ (p2 ∨ (p3 ∧ ((p2 ∧ p3) ∧ p3)))) ∧ (((p2 ∨ p3) → (p3 ∨ p3)) ∨ p5)) ∨ ((p2 ∧ p1) → p1)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- False on the left can always be used.
  apply False.elim h6
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : (((p5 ∨ (p2 ∨ (p3 ∧ ((p2 ∧ p3) ∧ p3)))) ∧ (((p2 ∨ p3) → (p3 ∨ p3)) ∨ p5)) ∨ ((p2 ∧ p1) → p1)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- One of the premise coincides with the conclusion.
    exact h10
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h11 := h1 h7
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42739076805175190007427473422 : (((True → ((p1 → (False ∨ ((p5 ∧ False) ∨ (p5 ∨ (p2 ∨ (p3 ∨ ((False → p2) ∨ p3))))))) → ((True ∧ (p5 → p2)) ∧ False))) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118643422215180170419938839873 : ((p4 ∨ ((True ∨ p5) → (((False ∨ ((p1 ∨ (p5 ∧ True)) ∧ (p1 ∧ (p4 ∨ p1)))) ∨ p5) ∨ ((False ∨ False) ∧ (p5 → p1))))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_805056788142913409549264891016 : (((p3 → (True ∧ (((p2 → p4) ∧ ((p5 ∨ (p3 ∨ p5)) → False)) ∨ ((p3 ∧ p4) → (((p4 → p5) ∨ ((False ∧ p1) → p4)) ∧ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729716374035368081810309985935 : (((((p2 → p2) ∨ p5) → (p3 ∧ (p4 ∧ (((((p2 → p3) → p4) ∨ (p2 → ((p3 → (True ∨ (p2 → p5))) ∧ p5))) → False) → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147816635405665415391369538520 : (((p5 ∧ ((p2 ∧ (((False ∧ (True ∨ (True ∨ p4))) → p3) ∧ (p1 ∨ (p4 ∨ p3)))) ∧ (p3 ∧ p1))) → p4) ∨ ((p3 ∧ False) → (p1 ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345295372605269649646563099204 : (p3 → ((p3 → ((((p2 ∧ p3) ∧ (p2 ∧ ((p3 ∧ (p4 ∧ p1)) → (p4 ∧ (((True ∧ p1) ∨ (p3 ∧ p3)) ∨ p4))))) → p1) ∨ p3)) ∧ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150319706988360742167771659173 : ((p4 → (p3 ∨ (((False ∧ ((p3 → (p2 ∨ p1)) → p1)) ∧ ((True ∧ p5) ∧ (p2 → p1))) ∨ (False ∧ p2)))) ∨ (True ∨ ((p2 → False) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50356221248904425450797242251 : (((((p2 ∧ (p1 → p1)) ∨ p5) → ((p5 → ((True → (p4 → p5)) ∨ (True ∧ (p5 → True)))) → p3)) ∨ (True ∧ (p4 ∧ (p1 → p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117650502486779635133244990667 : ((p3 ∧ ((((p3 ∨ (False ∨ True)) ∧ p1) → (False ∨ (((True ∧ ((p5 ∨ (p5 ∧ True)) → False)) ∨ p1) ∨ p4))) ∧ (True ∧ p5))) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260204903550463743793738907617 : ((p2 → p2) → (p1 ∨ ((((p3 → p5) → (p2 ∨ p4)) → (p4 ∨ p1)) → (((p5 ∧ True) ∧ False) ∨ (False → (p4 ∧ ((p2 ∨ p2) ∨ p1))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199736210643862150261279931960 : (((p2 ∨ (((True ∧ p4) ∧ True) ∨ True)) → False) → (False ∧ ((p3 ∧ (p2 → (p1 ∨ ((False → (False ∧ (p1 → False))) ∨ False)))) ∧ (False → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 ∨ (((True ∧ p4) ∧ True) ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : (p2 ∨ (((True ∧ p4) ∧ True) ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : (p2 ∨ (((True ∧ p4) ∧ True) ∨ True)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h7
  -- False on the left can always be used.
  apply False.elim h8
  -- Implications on the right can always be decomposed.
  intro h9
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171145839729636272810937610883 : ((p1 → (((p3 ∨ ((False ∧ (p2 ∨ p2)) ∧ ((p4 ∨ p2) → p4))) ∨ p1) ∨ p1)) ∧ (p4 ∨ (False ∨ (((p1 → p1) ∨ (p5 → p5)) ∨ p4)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_908850721067596555423373036244 : ((((((((p4 ∧ (p4 → (p4 ∧ p3))) ∨ p1) ∨ (p2 ∨ False)) ∧ (p1 ∧ p5)) ∨ (p5 → p1)) ∧ (p5 ∧ (((False ∨ p2) ∨ p5) → False))) → p4) ∧ True) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Conjunctions on the left can always be decomposed.
        let h11 := h6.left
        let h12 := h6.right
        -- Conjunctions on the left can always be decomposed.
        let h13 := h3.left
        let h14 := h3.right
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h6.left
        let h17 := h6.right
        -- Conjunctions on the left can always be decomposed.
        let h18 := h3.left
        let h19 := h3.right
        -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
        have h20 : ((False ∨ p2) ∨ p5) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h18
        -- We have shown the premise of h19, we can now drive its conclusion.
        let h21 := h19 h20
        -- False on the left can always be used.
        apply False.elim h21
    case inr h22 =>
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h23 =>
        -- Conjunctions on the left can always be decomposed.
        let h24 := h6.left
        let h25 := h6.right
        -- Conjunctions on the left can always be decomposed.
        let h26 := h3.left
        let h27 := h3.right
        -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
        have h28 : ((False ∨ p2) ∨ p5) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h26
        -- We have shown the premise of h27, we can now drive its conclusion.
        let h29 := h27 h28
        -- False on the left can always be used.
        apply False.elim h29
      case inr h30 =>
        -- False on the left can always be used.
        apply False.elim h30
  case inr h31 =>
    -- Conjunctions on the left can always be decomposed.
    let h32 := h3.left
    let h33 := h3.right
    -- We want to use the implication h33 based on <expert-advice>. So we show its premise.
    have h34 : ((False ∨ p2) ∨ p5) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h32
    -- We have shown the premise of h33, we can now drive its conclusion.
    let h35 := h33 h34
    -- False on the left can always be used.
    apply False.elim h35
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_595698761005822821562263364141 : (((((p5 → ((((p3 → (False ∨ p4)) ∧ p2) ∧ True) → (p2 ∧ p2))) → (p3 ∧ ((p3 ∨ False) → (((p5 → True) ∨ True) ∨ p4)))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186002967768472096192423311521 : (((p5 ∨ (p4 ∨ (p2 → ((p1 → p1) → (p4 → p2))))) ∧ p1) → ((p1 → False) → (((((p1 → (True ∨ p4)) ∨ False) → p4) ∧ p2) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h9 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h10 := h2 h9
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h13 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h14 := h2 h13
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h16 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h17 := h2 h16
      -- False on the left can always be used.
      apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44715333380248280830212299615 : ((((p1 ∨ (p1 ∨ (p2 ∧ p1))) ∧ ((((((p3 ∨ (p5 ∨ False)) ∧ p5) → p5) → (p2 → (p3 → (p1 → True)))) ∨ p4) ∨ True)) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252432771178165260828874975315 : ((p5 → False) ∨ (p3 ∨ (((p3 ∧ (p3 ∧ ((((((False ∧ False) ∧ p3) ∨ ((p2 ∨ p5) ∨ (p1 ∨ False))) ∨ False) → p3) ∨ p2))) ∨ True) ∨ p5))) := by
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
theorem thm_5_vars_657879712048730089717461835207 : ((((False ∧ (p3 → ((p2 ∨ ((False ∨ False) → (p5 ∨ (True → (p4 → p3))))) → (p2 ∧ (((p2 ∨ True) ∨ False) → p3))))) ∨ (p2 ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50531530667135877934594620916 : ((((((((p1 → p3) → False) → p4) ∨ ((p4 ∧ (p1 ∧ p2)) ∨ ((p4 ∨ False) ∨ p1))) ∨ False) ∨ p3) → (p4 ∧ ((p4 ∨ p1) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_592148265354363257924285405140 : (((((p5 → ((False ∨ (p4 ∨ p2)) ∧ ((p2 ∨ (((p4 ∨ False) → p5) ∧ p4)) ∧ (p1 ∧ (p3 ∧ (p4 ∧ p1)))))) ∨ (p4 → True)) ∧ True) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_251127819021320332231240358736 : ((p2 → False) ∨ ((p2 ∧ (((p3 ∨ p4) ∧ ((((p3 ∧ (((False → p1) ∧ p2) → p4)) ∧ True) → True) → False)) ∧ p3)) ∨ (False ∨ (False → p1)))) := by
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
theorem thm_5_vars_206001775872201887751285487097 : ((p1 ∧ (True → ((p4 ∨ p3) ∨ False))) ∨ ((True ∧ (((((False ∧ p4) ∨ p2) ∧ (p3 ∨ p3)) → p1) ∨ (p5 → False))) → (p1 → (False ∨ p1)))) := by
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
  cases h4
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658665721463723087858083888660 : ((((p4 ∨ (((p3 ∧ p5) ∧ ((p5 → (((p4 → p3) → ((p2 → p5) ∨ (False ∧ p1))) → p2)) ∨ (True → p4))) ∨ True)) ∨ (p5 ∧ p5)) ∨ p2) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345528416395183057314197396197 : (p3 → ((((((p1 ∨ p1) ∨ p4) ∧ p5) ∧ (p2 ∧ (True ∧ False))) ∨ ((False ∨ (p1 ∨ ((True ∨ (True ∧ p5)) ∨ (p1 ∨ p5)))) ∨ p5)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53919795977736434429531379020 : (((p2 ∨ ((p2 ∨ (((p4 ∧ p3) ∨ True) → p1)) → p2)) ∨ ((((False → p3) ∧ (p1 → True)) ∧ True) ∨ (p2 ∧ ((p4 ∨ p3) ∧ True)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37434270456227466439284351958 : ((((((((p2 → ((p1 → p3) → False)) ∨ p4) ∨ p4) → ((p2 ∧ p3) → (p3 → p5))) ∧ (p2 ∨ ((p5 ∨ p3) → p5))) ∨ False) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226516287116685908552990461990 : (((p3 → False) ∨ p5) ∨ ((((((p1 → (p3 → p4)) ∨ p1) → (False ∨ ((p1 ∨ (((p2 ∨ p3) → p3) ∨ p2)) ∨ p5))) → p2) ∧ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260667572790096834172014022616 : ((p3 → p3) → (((((True ∨ False) → (False ∧ (p3 ∨ p2))) ∧ p3) ∧ (p2 → (True ∧ p3))) ∨ (((True ∧ (False → (p4 ∨ p1))) → p4) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310121435751310250203698796867 : (p2 ∨ (((False → (p5 ∨ (p5 ∧ ((p5 ∧ (False ∧ p5)) → p3)))) → (False ∧ p1)) ∨ (False → (p2 ∨ (p2 → (((False ∨ p3) → True) ∨ p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345372832508956019353216052300 : (p3 → (((((False → ((p4 ∧ p2) ∨ True)) ∨ False) → ((p5 ∧ (p2 → (False ∧ (p4 → (p5 ∨ ((True ∧ p3) ∨ p1)))))) → p2)) ∨ p5) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165371865382958179050941704114 : (((((p5 → (False → (((True ∨ p4) ∨ p3) → True))) ∨ p2) → p4) ∨ ((True ∨ p2) ∧ p1)) ∨ (((p2 → False) ∨ False) → (True ∨ (True → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683582127958509409862145149873 : ((((((((p5 → p4) ∧ p5) → (p1 ∧ (p1 ∨ (p2 ∧ (p3 ∨ (True ∧ False)))))) ∨ p2) ∧ p4) ∨ (((True → p2) → True) ∨ (p1 → p2))) ∨ p5) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200436964952200012231905675890 : (((p4 ∨ False) ∨ ((p3 ∧ p3) → (p3 → p4))) → ((((p1 ∧ (p1 → p1)) ∨ p4) ∨ (False ∨ ((p3 ∨ p3) ∨ (True ∨ (p1 ∨ p5))))) ∨ False)) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h4 =>
      -- False on the left can always be used.
      apply False.elim h4
  case inr h5 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_660693269693388147247806402012 : ((((((p3 → ((p5 ∨ (p3 ∧ ((p5 → False) ∨ False))) ∨ True)) ∨ (p4 ∨ ((p3 → ((p4 ∧ p3) ∧ p4)) ∧ p2))) → False) → (p1 ∨ p1)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p3 → ((p5 ∨ (p3 ∧ ((p5 → False) ∨ False))) ∨ True)) ∨ (p4 ∨ ((p3 → ((p4 ∧ p3) ∧ p4)) ∧ p2))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57496199429338333672375791172 : (((p2 → (p4 ∧ p3)) ∨ (False ∨ (((p5 ∨ p1) ∨ p5) → ((p5 ∨ (p3 ∧ p4)) ∧ ((p3 → False) → ((True ∧ False) ∨ (p3 → p5))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234919692503164272467328695749 : ((True ∧ True) ∧ ((False ∨ ((((False ∧ (p4 ∨ p1)) ∨ (p1 → True)) ∨ False) ∧ p4)) ∨ ((p3 → p3) ∨ (p4 → ((p1 ∨ p2) → (True → False)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116990140564708091758268206507 : (((True ∨ True) → ((p3 → p1) → ((p2 ∨ ((p3 → (p5 ∨ (False → ((p4 ∧ (True ∨ False)) → p5)))) ∨ (p3 → p5))) ∧ False))) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192864345918256936117689904668 : (((((p3 → p2) ∧ True) → (p5 ∨ p2)) ∧ (p2 → p2)) → (((((p2 → True) → (p5 ∧ (True ∧ p4))) ∨ False) ∨ (False ∨ (False ∨ True))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
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
theorem thm_5_vars_200533493185349117061560386895 : (((p4 ∨ p5) → ((False ∧ p1) ∧ (False ∧ p3))) → (((p5 → (p2 ∨ p4)) → (False ∨ False)) → ((True ∧ p4) ∧ ((p5 ∧ False) ∨ (p3 ∧ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p5 → (p2 ∨ p4)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h5 : (p4 ∨ p5) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h6 := h1 h5
    -- We need to get the left conjuct of h6 based on <expert-advice>.
    let h7 := h6.left
    -- We need to get the left conjuct of h7 based on <expert-advice>.
    let h8 := h7.left
    -- False on the left can always be used.
    apply False.elim h8
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h3
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h12 : (p5 → (p2 ∨ p4)) := by
    -- Implications on the right can always be decomposed.
    intro h13
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h14 : (p4 ∨ p5) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h13
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h15 := h1 h14
    -- We need to get the left conjuct of h15 based on <expert-advice>.
    let h16 := h15.left
    -- We need to get the left conjuct of h16 based on <expert-advice>.
    let h17 := h16.left
    -- False on the left can always be used.
    apply False.elim h17
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h18 := h2 h12
  -- Disjunctions on the left can always be decomposed.
  cases h18
  case inl h19 =>
    -- False on the left can always be used.
    apply False.elim h19
  case inr h20 =>
    -- False on the left can always be used.
    apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166107408159210414018422275555 : (((p4 → True) → ((((p5 ∧ True) → p1) ∧ (((True ∧ p2) ∨ False) → (p2 ∨ p5))) → p4)) ∨ ((((p4 ∧ True) ∨ True) ∨ True) ∨ (p4 ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116513145919202628555018717728 : (((p4 ∧ p4) ∧ (p2 ∧ ((p3 ∨ ((((((p2 ∨ p2) ∨ (p4 ∨ p3)) ∨ (p5 → p3)) → True) ∨ (p1 ∧ p1)) → False)) ∧ p1))) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47082972529840485058577965804 : ((((((p5 ∨ (p4 ∧ (p2 → (((p2 ∨ p2) ∨ (p2 ∧ p3)) ∨ p1)))) → p4) ∧ (p1 → (False ∧ p5))) → (p4 ∨ p5)) ∨ (True ∨ p3)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168583697986590027276084824010 : ((p2 ∧ (((p2 → (p4 ∧ p2)) ∨ False) → (p3 → (((p4 → p1) → False) ∨ (False → False))))) → ((p1 → ((p5 ∨ p1) ∧ (p2 → p5))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249224900117631684135088361876 : ((p4 ∨ p4) ∨ (((((p3 ∨ p4) ∧ p4) ∨ ((p2 ∧ p1) ∨ (p1 ∨ p3))) → (((p2 ∨ True) ∨ (p4 ∧ ((p2 → False) ∧ False))) ∧ True)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h13 =>
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



