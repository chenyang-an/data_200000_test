variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55445788423019476593155552870 : (((((p1 ∧ False) ∨ (p2 → p2)) → p3) → (((p1 ∨ False) ∧ (p2 ∧ ((p4 ∨ (p3 → p4)) ∧ (p3 ∧ (p5 → (True → False)))))) → p4)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h9.left
      let h12 := h9.right
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h9.left
      let h15 := h9.right
      -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
      have h16 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h14
      -- We have shown the premise of h13, we can now drive its conclusion.
      let h17 := h13 h16
      -- One of the premise coincides with the conclusion.
      exact h17
  case inr h18 =>
    -- False on the left can always be used.
    apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_688043814668915969255251255604 : (((((p3 → ((p4 → (True ∨ p3)) → p3)) → ((p5 → (p4 ∨ (p5 ∧ p4))) ∧ p3)) ∧ (((p2 ∧ p2) → p1) ∨ ((False → p3) → True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315378053105312246399243208171 : (p3 ∨ ((False → (False → False)) ∧ ((((True ∧ ((p1 ∧ (p1 ∧ (p2 ∨ (p5 ∧ p2)))) → True)) ∧ True) → False) → (((p1 ∧ p1) ∨ p3) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((True ∧ ((p1 ∧ (p1 ∧ (p2 ∨ (p5 ∧ p2)))) → True)) ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256943590171384702412011609253 : ((p1 ∨ p5) → ((((p4 ∨ p2) ∧ (p2 → p2)) ∨ (False ∨ (p3 ∨ (((((((p5 → True) → True) ∨ p4) ∨ p2) ∨ p3) ∨ True) ∨ p3)))) ∨ p3)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
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
theorem thm_5_vars_58062663047928292817258917981 : (((False ∧ p3) ∧ (((False ∨ ((p5 ∨ p1) ∨ (p1 ∧ ((((p5 ∧ p3) ∨ (True ∨ (p1 ∨ False))) → (p1 ∨ p5)) ∨ p4)))) ∨ p3) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_642241987843517580661533782517 : ((((True ∧ (True → ((p1 ∨ False) → ((((p3 ∧ (p1 ∨ p4)) ∨ (False → (False ∧ p1))) → p4) → ((p2 ∧ (p3 ∨ p4)) ∧ p5))))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351411407066046045079779183087 : (p4 → (((p2 → ((p1 → True) → True)) → (p2 ∧ (((p2 ∨ p4) ∨ False) ∧ (p3 ∧ (p5 ∨ (p2 → p1)))))) ∨ (((True → p4) ∧ False) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197384209988166105909060110168 : (((p2 ∨ (True ∨ (False ∨ (p5 → False)))) → p1) ∨ (((p3 ∧ (p3 ∨ (((True ∧ p1) → (p3 ∧ (p5 ∨ p3))) ∧ False))) ∨ (p5 → True)) ∨ p1)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42255279603384736178319928722 : (((p1 ∧ ((((p2 ∧ (p4 → p1)) ∨ True) ∧ (((p1 ∧ (True ∧ p3)) ∧ (p5 → p4)) ∨ (((True ∨ p2) ∨ p1) ∧ p3))) ∨ p1)) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_603850624725326361632570731746 : ((((p4 ∨ (p3 ∧ ((p5 → ((p2 ∧ True) ∧ False)) ∨ ((p3 ∧ (p1 ∨ p1)) → ((p2 ∧ ((True ∧ p4) → p3)) ∨ (p1 ∧ p5)))))) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111422136456680123729222586458 : (((p3 ∨ (p5 ∨ (((p3 → (False ∧ p3)) ∧ (p5 ∨ (p1 ∧ (p2 ∨ p4)))) ∨ ((p5 ∧ (False ∧ p4)) → (True ∨ p5))))) ∧ True) ∨ (p2 ∨ p5)) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60463207279552563329005402187 : (((p5 → p3) → (((p3 ∧ (((True → True) ∧ p3) → ((True ∨ (p3 ∧ True)) ∧ ((p1 ∧ True) ∨ ((p4 ∧ True) → p1))))) ∨ True) ∧ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303872794325016308591876157565 : (p1 ∨ (((p5 ∧ (p4 ∧ (((((p3 ∧ p1) ∧ p2) → p3) ∨ (p3 ∨ (p2 ∨ ((p3 → p4) → p5)))) ∨ False))) → (p1 ∨ (p4 ∨ p5))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301153649274898421963333466979 : (False ∨ (((p3 ∨ p2) ∨ ((p5 ∨ p1) ∨ (True → True))) ∨ (((True ∧ p1) ∧ p3) ∨ ((p5 ∨ p1) ∧ ((p1 ∨ p5) → (p3 → (p5 ∧ p2))))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353556701173738028445998787687 : (p4 → (p3 ∨ (((False → (p4 → (True ∧ p3))) ∨ (True → (p2 ∨ p5))) → (True ∧ ((((((False → p5) ∧ p3) ∧ p1) ∨ True) ∧ p4) ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171328152229743673890129284657 : ((((False ∧ (((True ∧ ((p1 ∧ p5) ∧ p5)) → (False ∧ p2)) ∧ False)) ∨ True) ∧ p5) ∨ ((((p2 ∧ False) → p4) → ((False ∧ p3) ∨ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50651408908750976572864020816 : ((((((((p1 → p1) ∧ p4) → (True ∧ p4)) → True) ∨ False) → (p3 ∨ ((p4 ∧ (p1 → True)) ∨ True))) → (((p1 → p5) → p2) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149916979883776231755837525770 : ((p3 ∨ ((((p4 ∨ p3) ∧ p3) → (((p1 → (p4 ∨ p1)) ∧ ((p4 ∧ p4) ∨ (False ∧ p1))) ∧ False)) → p2)) ∨ ((p4 ∨ (p4 ∨ p4)) → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- One of the premise coincides with the conclusion.
      exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356043393299771763100241403935 : (p5 → ((p3 ∧ (((((True → p2) ∧ ((p2 ∧ p4) ∨ p3)) → (True → (p2 ∨ p1))) ∧ p1) → (p3 ∨ p3))) ∨ ((True ∨ p3) ∨ (p4 → p5)))) := by
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
theorem thm_5_vars_737633825842570003777468692143 : ((((p5 → p3) ∧ ((((((True ∨ p2) ∧ False) ∧ p3) ∨ ((((((p3 ∨ p4) ∧ p3) ∨ p3) ∧ p2) → (False → True)) ∨ p4)) → p5) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610116398171077006442172941274 : ((((((p5 ∧ ((((((p2 ∨ ((True ∨ (p3 → (p1 ∧ True))) ∨ (True → p5))) ∨ p4) → p3) ∧ p3) → p5) ∧ True)) ∧ p5) → p1) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_41406319470775688291532283915 : (((((p2 → (((((p3 ∧ p5) ∨ (False ∧ p2)) ∧ False) ∨ p3) ∧ p4)) ∨ p1) ∨ ((False → (((p4 → p3) ∨ p3) ∨ p1)) ∧ p1)) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_706524178192813996085900564420 : ((((True → ((((p3 → p4) ∨ True) ∧ p4) ∧ p3)) ∧ (p4 ∨ ((p3 ∧ False) ∨ (p5 ∧ (p5 ∧ (p1 → (p4 ∧ ((False ∧ p5) ∨ p5)))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178479114722505958105379927189 : (((((p1 ∨ (False ∨ False)) → (True → p3)) → p1) ∨ (p5 → (False → True))) ∨ ((p3 → (p2 ∧ True)) ∨ ((p5 → ((p5 ∨ True) → False)) → p1))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56065723176339131827736171581 : (((((p3 → p5) → p3) → p3) ∨ (((p3 → ((p3 ∨ p2) ∨ p2)) ∨ (True ∧ (p4 ∨ (p2 → p3)))) ∧ ((p3 ∧ p3) ∨ (p2 ∨ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351639139427683470784376440945 : (p4 → (((((p1 ∨ p4) ∨ p2) ∧ p5) ∧ (((False → True) → ((p2 → p3) ∨ False)) ∨ False)) ∨ (True ∨ (True ∧ ((p1 ∧ p2) ∨ (p1 → p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157505020427644999072277421672 : ((((False → p4) → (((p3 ∨ p4) ∨ ((((True → p1) ∧ True) ∨ p3) ∨ p3)) → p2)) ∨ (p2 ∨ True)) ∨ ((p4 → (p3 → p1)) ∨ (p5 ∧ p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337656979557509811236208358560 : (p1 → ((((((p4 ∧ p4) ∧ p2) → (False ∨ (p1 ∧ ((True ∧ p3) ∨ p2)))) → p2) ∧ (p5 ∨ p1)) ∨ (False → ((True → p3) → (p5 ∧ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55067206774840505261318075606 : (((p4 ∨ (((p3 ∨ p4) ∨ p4) ∧ True)) ∧ (p4 ∧ (False ∨ ((((p4 ∧ p2) ∧ (p5 ∨ (False ∧ p1))) → p5) ∨ (p3 ∨ (p5 ∨ p2)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_901723683070223656210792407036 : (((((((p3 → True) → (p4 ∨ False)) ∨ (p2 ∨ ((False ∧ p3) ∧ (True ∧ (True ∨ (False ∨ p4)))))) ∨ p1) ∧ ((True → (p2 ∧ False)) ∧ p2)) → False) ∧ True) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h3.left
      let h7 := h3.right
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h8 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h9 := h6 h8
      -- We need to get the right conjuct of h9 based on <expert-advice>.
      let h10 := h9.right
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h3.left
        let h14 := h3.right
        -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
        have h15 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h13, we can now drive its conclusion.
        let h16 := h13 h15
        -- We need to get the right conjuct of h16 based on <expert-advice>.
        let h17 := h16.right
        -- False on the left can always be used.
        apply False.elim h17
      case inr h18 =>
        -- Conjunctions on the left can always be decomposed.
        let h19 := h18.left
        let h20 := h18.right
        -- Conjunctions on the left can always be decomposed.
        let h21 := h19.left
        let h22 := h19.right
        -- False on the left can always be used.
        apply False.elim h21
  case inr h23 =>
    -- Conjunctions on the left can always be decomposed.
    let h24 := h3.left
    let h25 := h3.right
    -- We want to use the implication h24 based on <expert-advice>. So we show its premise.
    have h26 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h24, we can now drive its conclusion.
    let h27 := h24 h26
    -- We need to get the right conjuct of h27 based on <expert-advice>.
    let h28 := h27.right
    -- False on the left can always be used.
    apply False.elim h28
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780984464934972611700978122637 : (((p2 ∨ ((True ∨ (p5 ∧ p5)) → ((((((False ∧ (p4 ∧ True)) ∧ p1) → (False → (p1 → p5))) ∨ p4) → p5) ∨ ((p3 ∨ True) ∧ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177635419544373160438980775895 : (((((p4 ∧ (p2 ∧ True)) ∧ (p3 ∨ ((p5 ∨ p4) ∨ p1))) ∧ True) ∧ p2) ∨ ((p3 → ((False → p2) ∨ p4)) → (p2 → ((p3 ∧ p5) → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67659834841128287245133606688 : ((p1 → (p4 ∨ ((p1 ∧ p2) ∧ (True ∨ (p1 ∨ ((False ∧ ((p3 → p4) → (((p5 → (p4 → False)) ∨ p2) ∨ (p1 ∧ p1)))) ∨ False)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654013279472338608177908634221 : (((((False ∨ (p4 ∧ (((False ∨ p5) → p2) ∨ (False ∧ (p3 → (p1 ∧ (((p4 → (True ∧ p4)) ∨ False) ∧ p1))))))) ∧ p5) ∨ (p5 → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140893346236193741258804442413 : ((((((p4 ∨ p2) ∨ p2) → (p3 ∨ (p4 ∨ False))) ∧ p4) ∧ (((False ∧ (p3 → ((p4 ∨ p5) ∨ p1))) ∨ p4) → p5)) → ((p4 → p2) ∨ True)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251681441767745051117224072966 : ((p3 → p2) ∨ (((p1 ∨ True) ∨ ((((p4 ∧ p5) ∨ True) → (p5 ∧ p3)) → p5)) → (True → ((((p4 ∨ p3) → (True ∧ False)) ∧ p4) → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h8 : (p4 ∨ p3) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h9 := h4 h8
      -- We need to get the right conjuct of h9 based on <expert-advice>.
      let h10 := h9.right
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h12 : (p4 ∨ p3) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h13 := h4 h12
      -- We need to get the right conjuct of h13 based on <expert-advice>.
      let h14 := h13.right
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h16 : (p4 ∨ p3) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h17 := h4 h16
    -- We need to get the right conjuct of h17 based on <expert-advice>.
    let h18 := h17.right
    -- False on the left can always be used.
    apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157326278330580714896351571809 : (((True ∨ ((((((p2 ∧ True) ∨ (p2 ∨ p4)) → (p2 ∨ (p1 → p4))) ∧ True) ∨ p5) ∨ False)) → p1) ∨ (p3 → (False → ((False ∨ p4) → p5)))) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50269048905228376431997059208 : ((((p3 ∧ ((((p2 ∧ True) ∧ (False ∧ (p2 ∨ ((p2 ∧ p4) → p1)))) ∧ p5) → True)) ∧ (False → p1)) ∨ ((p4 → p4) → (p5 ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133631571541174618664480446990 : ((((p4 ∧ ((p3 ∧ ((((p2 → True) → p3) → True) ∨ p2)) ∧ (((False ∧ True) ∨ p4) ∧ (p3 → p5)))) → False) ∧ p5) ∨ ((p1 → True) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233698898906263202884510847903 : ((p2 ∨ (p4 → False)) → (((p2 → (((p1 ∧ (p5 ∧ ((True → True) ∨ p4))) ∧ p4) ∧ False)) ∧ False) ∨ (p1 → ((p3 ∧ p4) → (p1 → p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h14 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h13
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h15 := h8 h14
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192118137961446965083310586012 : ((p5 → ((p4 ∧ (False ∨ (False ∨ (p1 ∧ p2)))) ∧ p1)) ∨ ((p3 → p1) → ((p5 ∨ ((True ∨ (p2 → (True ∧ p4))) ∨ (p1 ∨ True))) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_112721936901250370953547281665 : (((((p2 ∨ (False → True)) ∧ (p1 → (((p5 ∨ p3) → True) ∨ (p5 ∨ False)))) ∨ (((p4 ∨ (p4 → p3)) → p3) ∧ p4)) → p1) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264574017526528175319791054390 : (True ∧ ((p4 ∧ (p2 ∧ False)) ∨ ((p2 → (((p2 ∧ (p1 ∨ p2)) → False) ∧ (p2 ∧ p1))) ∨ ((((p3 ∧ False) → (p3 ∧ False)) ∨ p1) ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118703944399353512565143853600 : ((p5 ∨ ((((((p2 ∧ (True → ((p5 → p5) ∨ (True ∧ p5)))) ∨ ((p4 ∨ True) ∨ p2)) → p2) → p2) ∨ (True ∨ p3)) → p1)) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721867821404129302062864900434 : ((((p4 ∨ ((p3 ∧ p5) → p2)) → (((False ∧ ((((True → False) → (p1 ∧ False)) → (p4 ∧ True)) ∧ (True ∧ p5))) ∨ (False → False)) ∧ True)) ∨ p5) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_759597622058590605026497839316 : (((p2 ∧ (((p3 ∨ (p1 ∧ (False → p5))) → (p3 → (p4 ∨ ((p5 ∧ p4) → (p4 ∧ p2))))) → ((True ∨ True) ∧ ((p5 ∨ p1) → p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118741375896240442003273131711 : ((p5 ∨ (((True ∨ p4) → (p5 ∧ (p3 ∨ (True ∧ p3)))) → ((((((p2 → False) ∧ p5) ∧ True) ∧ (p2 ∧ False)) ∨ True) ∨ p3))) ∨ (p4 ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_731182759587760029742148913740 : ((((p2 ∨ (p3 → True)) → (False ∨ (((False ∨ (p3 ∧ (p3 ∨ (p3 ∧ p2)))) ∧ (p4 ∨ True)) → ((p2 ∨ p5) ∨ (p5 ∧ (p1 ∧ p1)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175415272690727168519871480609 : ((False → ((p4 ∧ p1) ∧ (((p5 ∧ ((True ∨ False) ∨ True)) ∨ (True ∧ p2)) ∨ p5))) → (((p5 → False) ∨ (p2 ∨ ((p4 ∧ False) → p4))) ∨ p5)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66590035350158956226492384812 : ((True → (((p2 → (((p2 ∧ False) ∧ False) ∨ ((p1 ∧ (True ∧ (True ∨ ((p5 ∧ p3) ∨ True)))) ∧ p3))) ∨ p1) ∨ ((p4 ∧ p1) ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58222330011234331742179367526 : (((p4 ∧ p3) ∧ ((((False → ((False ∨ (p3 ∨ p1)) → p4)) → p5) ∧ p3) → (False ∨ (p3 ∧ ((p4 ∧ (p5 ∧ (p4 → True))) ∧ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337944417918067578832892303712 : (p1 → ((((p2 ∧ (p4 ∨ (p3 ∨ (False → p2)))) ∨ (p3 ∨ p4)) → False) ∨ ((((p3 ∧ (p4 ∧ p2)) ∨ p5) ∧ (False ∧ (p2 ∧ p5))) → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h4.left
    let h11 := h4.right
    -- False on the left can always be used.
    apply False.elim h10
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h4.left
    let h14 := h4.right
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219264775112512838131714988196 : ((p1 ∨ (p1 ∨ (True ∧ True))) → (p3 → (((p5 → ((p5 ∨ False) ∧ p3)) → p5) ∨ (p2 ∨ (True ∨ ((True ∨ p3) → (p3 ∨ (p3 ∨ p2)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727391203297992549528812844174 : ((((p2 ∧ (False → True)) ∨ ((((False ∧ p1) ∧ p2) ∨ (p2 → ((p3 ∨ p3) → (p5 → (p1 → (p4 ∧ p3)))))) → ((False ∧ p1) ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702294500133466031146534895989 : (((((False ∨ ((p1 ∨ (p1 → (p2 ∨ p5))) → p5)) ∧ p1) ∨ ((False ∨ (p5 → p4)) ∨ (p4 → (p5 → ((p4 ∨ False) ∧ (p2 ∨ p5)))))) ∨ p4) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671789915091505706483500542617 : (((((((p4 ∧ (p4 → False)) ∨ p4) → (((True ∧ ((True ∧ ((p4 ∧ p1) ∨ p4)) ∨ True)) → p3) ∧ p5)) ∧ p3) → (p4 → (p1 → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180569031002987562179729329417 : ((((p3 → (((p1 ∨ p5) ∨ False) ∧ p4)) → True) → ((True → True) → False)) → (((((((p3 → p5) → p1) → p1) ∧ p5) ∧ False) ∨ p3) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p3 → (((p1 ∨ p5) ∨ False) ∧ p4)) → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : (True → True) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h5
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_681339840743976793692071087945 : ((((False ∨ ((p1 ∨ p3) → ((p5 → (True ∨ ((p3 ∧ False) ∧ (True → (True → p1))))) ∧ (False ∧ p1)))) → ((p4 ∨ (p5 → p2)) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156694650206333639347812430672 : (((((((True ∨ p2) → p3) → ((p4 ∧ (p4 ∨ p4)) ∧ p5)) ∨ p1) ∨ (p3 ∨ (p1 → True))) ∧ p5) ∨ ((p2 ∧ p4) ∨ (p3 → (p3 ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178710711797137467806182400062 : (((p5 ∨ (p4 ∨ (p4 ∨ p3))) ∨ (p1 → ((p3 → (p2 ∨ False)) → False))) ∨ ((((False → p5) ∧ (p5 ∨ (p5 ∧ (False ∨ p5)))) ∨ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159268755046099211531774456860 : ((p4 → (((p5 ∧ (((p5 ∨ p2) ∧ (True → ((p3 → p2) ∧ False))) → False)) ∨ (True ∧ p1)) ∨ p4)) ∨ ((False ∧ (p2 ∨ (p2 → p1))) → p4)) := by
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
theorem thm_5_vars_160519712452527731309315608536 : (((((False → (False ∧ p2)) ∨ ((p2 ∧ p4) → (p2 ∧ p5))) ∧ p5) ∨ (((p3 → p3) ∧ p2) → True)) → ((p2 ∨ False) ∨ ((p5 → True) ∨ p5))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h10
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136138521614342950568613969846 : (((((p3 ∨ (p3 ∨ (p2 ∨ p2))) → True) → p1) → ((False ∧ (p1 ∧ ((False ∨ (p4 ∧ (p5 ∧ p2))) ∨ False))) ∨ p2)) ∨ ((p1 ∧ p3) → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308383745867173761564750231506 : (p2 ∨ ((((p1 → ((((True ∧ (p1 ∨ p4)) ∨ ((p5 ∧ p2) ∧ (True ∧ p4))) ∨ p4) → True)) → ((p5 → False) ∨ (p1 ∧ False))) ∨ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_751446062537888260906249699330 : (((True ∧ ((p5 ∨ p4) → ((((p4 ∨ p4) → ((p2 ∧ False) ∨ p3)) ∨ p3) ∨ (False → (((p1 → (p5 ∧ False)) ∨ p1) → (p1 ∨ p2)))))) ∨ p2) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h3
    case inr h6 =>
      -- False on the left can always be used.
      apply False.elim h3
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- False on the left can always be used.
      apply False.elim h8
    case inr h11 =>
      -- False on the left can always be used.
      apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43516340597494131463069838760 : ((((p4 ∨ (((True ∧ (p3 → True)) → (((((p5 → (p5 → p5)) ∨ True) ∨ True) → True) ∨ (False → (False → True)))) → p5)) ∨ p3) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184298524869910949841281799357 : (((((p5 ∧ p5) ∧ False) ∨ ((True → True) ∨ (True ∨ p4))) → p4) ∨ ((False ∨ True) ∧ ((p2 → p2) ∧ (p2 ∨ (((p3 ∨ p5) ∧ True) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166937067939784046848776949960 : ((((p3 ∧ p2) ∧ (p2 ∧ ((p4 ∧ (p2 → False)) → ((p2 ∧ (p4 ∨ p2)) ∧ p1)))) ∧ p2) → ((p5 → p4) ∨ (p4 ∨ (p5 ∨ (False ∨ p3))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h5.left
  let h9 := h5.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_719452130174677664934239360423 : ((((p1 ∨ ((p2 → p4) → p1)) ∨ (((((p5 → (p2 ∨ p1)) ∨ True) ∨ p1) ∨ (p4 ∧ (p5 ∨ True))) ∨ ((p5 ∨ True) ∨ (False ∨ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172850164899692620203963693293 : ((False ∧ (((p2 → (p5 → p1)) → p5) ∨ (p5 ∧ (True → (p4 ∨ (p3 ∧ True)))))) ∨ (((p1 ∨ p3) → ((p1 ∨ (p5 ∨ p1)) ∧ p3)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_104555235474126393975010076581 : (((((p5 ∨ (p2 ∨ p4)) ∨ (False ∧ ((p2 ∧ ((p2 ∨ (True → (p4 ∧ p2))) → p5)) → p2))) ∨ (p1 → True)) ∨ (True ∨ p1)) ∧ (p1 ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234092571904444458573426817007 : ((True → (p4 ∧ False)) → (((p2 ∧ (False → (p1 → p2))) ∨ (p5 ∧ p2)) ∧ (((False ∧ p5) ∨ ((((p3 → p1) ∧ p3) → p2) → True)) → p3))) := by
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
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h9 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h10 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h11 := h1 h10
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177736205609114698204393414147 : ((((p1 ∨ (False → p5)) ∧ (p1 → ((p2 ∨ (p1 ∧ p5)) ∨ p4))) ∧ p3) ∨ ((p2 ∨ True) ∨ (((p5 ∧ (p2 ∧ (False ∨ True))) ∨ p3) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351565659127663971247086094684 : (p4 → ((((p2 → (((p3 ∧ (p3 ∧ True)) ∧ p3) → ((p5 ∧ p5) → p1))) → p1) → (p2 → p4)) → (True ∧ ((p2 → p3) ∨ (p4 ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_641971524432624953020196518244 : (((((p5 → p1) → ((p3 ∨ (((p1 → p4) ∨ True) → ((p1 ∧ ((p3 ∨ p2) ∨ (False → p4))) ∧ (True → (p3 → p3))))) ∧ p4)) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221509602960791973989226287745 : (((p2 → True) ∨ p2) ∧ ((p3 ∨ ((p1 → ((p4 → p3) → ((p5 ∨ p5) → p4))) ∨ True)) ∧ ((p3 ∧ ((p4 ∧ p1) ∨ False)) → (True ∧ p4)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59881137074329505867134536230 : (((p4 ∧ p4) → ((p2 ∧ (p1 ∧ ((False ∨ (p3 ∨ p5)) ∧ (p3 → p5)))) ∨ ((False ∨ p4) ∧ (((p5 → p4) → (p4 ∧ p4)) ∨ p1)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111582921518138968476908803183 : ((((p3 ∧ (p1 → ((p3 → p4) ∨ (p4 ∨ ((((p2 ∧ (p3 → p4)) ∧ (True → (p3 → p4))) ∨ p2) ∧ p3))))) ∧ p5) ∨ True) ∨ (False → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_623612025913036614057635082674 : ((((False ∨ (p5 ∨ ((True ∧ (p3 ∨ p4)) → (((p5 ∧ ((p1 ∧ (((False ∨ p1) ∧ p4) → False)) ∨ (p4 → p1))) ∧ p3) → p1)))) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_633524465798678366760331701084 : (((((((p3 ∧ (((p3 ∨ p1) → p5) ∨ p1)) ∨ ((p4 ∨ p5) ∧ p3)) → (((False ∨ (p1 ∧ p1)) ∧ True) → p1)) ∨ (p1 ∨ p3)) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315061533112933708025989682252 : (p3 ∨ ((False ∨ ((True ∨ p3) ∨ (p4 ∧ (True → True)))) → ((p2 ∨ ((p3 ∨ p5) ∧ p4)) ∨ (((p2 → (p4 ∧ (p5 ∧ p1))) ∧ p2) → p4)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h6
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h9 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h8
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h10 := h7 h9
        -- We need to get the left conjuct of h10 based on <expert-advice>.
        let h11 := h10.left
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h13
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
        have h16 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h15
        -- We have shown the premise of h14, we can now drive its conclusion.
        let h17 := h14 h16
        -- We need to get the left conjuct of h17 based on <expert-advice>.
        let h18 := h17.left
        -- One of the premise coincides with the conclusion.
        exact h18
    case inr h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h19.left
      let h21 := h19.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h22
      -- Conjunctions on the left can always be decomposed.
      let h23 := h22.left
      let h24 := h22.right
      -- One of the premise coincides with the conclusion.
      exact h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45098804999158917638145134292 : ((((True ∨ p5) → (p2 → (p2 ∧ (((((False → p1) ∨ p4) ∧ (p1 ∧ p2)) → True) ∨ (p2 ∧ (p1 ∧ ((False → p2) ∧ p2))))))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199051531336274692074978516935 : ((((p2 ∧ ((True → p1) → p4)) ∨ p4) ∧ p3) → ((True → ((p3 ∧ ((True ∧ True) ∨ p2)) → (False → p5))) → ((p5 ∨ (p5 → p5)) ∨ p4))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345319815498127423501849808931 : (p3 → ((((((p4 → ((p1 ∨ (False → p4)) ∨ p2)) → (p4 ∨ ((True ∧ (((p5 ∧ p2) ∧ False) ∨ p5)) → False))) → p2) → False) ∧ p3) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705831900757754679580945183729 : ((((((p4 ∧ False) ∧ p4) ∧ ((p2 ∧ p5) ∨ p5)) ∧ (((p4 → (p1 ∨ True)) ∨ ((p3 ∧ p1) → ((False ∧ p4) ∨ True))) ∨ (p3 → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258522978622067264999968512319 : ((p5 ∨ p3) → (((p1 ∨ p2) ∧ (((p3 ∧ ((p1 → (p1 → (p2 → (p4 → False)))) → (p3 → (p2 ∨ (p4 ∧ p1))))) ∧ False) ∨ p3)) ∨ True)) := by
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
theorem thm_5_vars_67310352116088833472996810360 : ((p1 → ((True ∧ (((p1 ∨ (p3 ∧ p4)) ∧ p2) ∨ (((p3 ∧ ((True → (p1 ∨ p3)) → (p4 ∧ p3))) ∧ (False → True)) ∧ p1))) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_781567990109780975434330213902 : (((p2 ∨ (False ∨ ((p2 → (p5 ∧ (p4 → p3))) ∨ (True → ((p3 → p4) ∨ (((((p5 → p5) ∧ (False ∧ p3)) ∨ p2) → p1) → False)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_696686230371933940229934115917 : (((((p2 → (p3 ∧ (p5 ∨ (p3 → (p3 → (p2 ∨ p5)))))) ∨ p3) ∧ ((p1 ∨ ((p2 ∧ (False ∨ p2)) → ((p4 → p1) ∨ p1))) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51574800755220640372141376352 : (((p3 ∨ (p4 ∨ (((((p1 ∨ p3) → False) ∧ (p3 → True)) ∧ ((p4 → p1) ∨ False)) ∧ p1))) → ((p3 ∨ p2) → (False ∨ (True → True)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Implications on the right can always be decomposed.
      intro h5
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h8
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Conjunctions on the left can always be decomposed.
        let h12 := h10.left
        let h13 := h10.right
        -- Conjunctions on the left can always be decomposed.
        let h14 := h12.left
        let h15 := h12.right
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h16 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h17
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h18 =>
          -- False on the left can always be used.
          apply False.elim h18
  case inr h19 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h20 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h21
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h22 =>
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h23 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h24
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h25 =>
        -- Conjunctions on the left can always be decomposed.
        let h26 := h25.left
        let h27 := h25.right
        -- Conjunctions on the left can always be decomposed.
        let h28 := h26.left
        let h29 := h26.right
        -- Conjunctions on the left can always be decomposed.
        let h30 := h28.left
        let h31 := h28.right
        -- Disjunctions on the left can always be decomposed.
        cases h29
        case inl h32 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h33
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h34 =>
          -- False on the left can always be used.
          apply False.elim h34



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607163174711847847940853157802 : ((((((p2 ∨ ((True → (p2 ∧ p3)) → False)) ∧ ((False → ((p4 → True) ∧ False)) → ((p1 ∨ p5) → ((False ∧ p2) ∨ False)))) ∧ p3) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111628269793095583200283737507 : ((((((((p1 → p5) ∧ p4) ∧ p1) ∨ ((p4 ∧ p3) ∨ (p4 → (p4 ∧ (p2 ∨ False))))) ∧ (p1 ∧ (p3 ∨ p5))) ∨ p1) ∨ False) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191558937902565142649529135835 : ((p1 ∧ (p3 ∨ (p2 ∨ (((p2 ∨ p1) ∧ True) → p1)))) ∨ ((p3 ∨ (((p5 → (((p2 ∨ p1) ∨ p4) ∧ (p3 → False))) ∨ p4) ∨ True)) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114773836493647277611878752346 : ((((((p1 ∨ False) ∨ p5) → (p2 ∨ (p2 ∨ ((p1 ∨ p1) ∨ p2)))) ∧ True) ∧ (p2 ∨ ((((p4 ∧ p4) ∧ p4) → p5) ∨ p1))) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116992704929725726186588431117 : (((True ∨ p1) → (((((p5 ∨ ((True ∨ p5) → ((p5 ∨ p3) → True))) → p4) ∧ (p2 ∨ (False → True))) → p4) → (p2 ∧ False))) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_644661636529941262298221203055 : ((((p1 ∨ ((p2 ∧ False) → (False → (p1 → (((((p5 ∨ (((p3 ∨ p1) ∧ p4) → p5)) → p1) ∧ True) ∨ p3) ∧ (p3 ∧ p2)))))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_752201905067369723083984961850 : (((True ∧ (p3 → ((((p5 ∧ (p2 ∨ p2)) → (p2 ∧ p5)) ∨ p3) → ((p4 ∨ ((p5 ∨ (p2 ∨ (True ∨ (p4 ∨ p4)))) ∧ True)) ∨ True)))) ∨ p2) ∧ True) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136669789545396613128225905946 : (((p2 ∨ (p3 ∨ False)) → ((p2 ∧ False) ∧ (p5 → (((True ∧ (p4 ∨ p2)) ∨ (p2 → (p5 → (p1 ∧ True)))) ∨ p3)))) ∨ ((p1 ∨ p4) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777393891300506063063940131980 : (((p1 ∨ ((((True ∨ (True ∨ False)) ∨ (((p3 ∧ True) → (p5 ∨ (p2 → True))) → p5)) → p5) ∧ (p4 → (((p3 ∨ True) ∨ False) → True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113378604239105899207189168074 : (((p3 ∨ (p2 ∨ ((True ∧ (((True ∧ p4) ∨ p1) → (((False → (p1 ∨ False)) ∧ p2) ∨ False))) ∧ (False → p3)))) ∧ (False ∨ p3)) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



