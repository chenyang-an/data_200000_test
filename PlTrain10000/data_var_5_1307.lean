variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148585983513075018827092801645 : ((((((p4 ∨ (False ∨ False)) → p3) ∧ p3) ∨ (p3 ∨ False)) ∨ (p4 → ((p3 → ((False ∨ p5) ∨ p2)) ∧ p2))) ∨ ((False → (False ∧ p1)) ∨ p5)) := by
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
theorem thm_5_vars_629845253716974037007060075616 : ((((((p2 → ((((p2 ∧ p3) ∧ p3) ∧ (False ∨ True)) ∨ True)) ∨ ((p1 → p3) → (p1 → (p5 ∧ ((p3 ∨ True) ∨ False))))) ∨ p1) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312131223198181832455761009588 : (p2 ∨ (True → ((True → (p1 → (((False ∧ p5) ∧ p5) ∨ (True → p3)))) ∨ (((p3 → p1) → (False → False)) ∧ ((p4 ∧ (False → p1)) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172208543650688952373525101315 : (((((p5 ∧ p5) ∨ p5) ∧ ((p2 ∨ (p1 ∨ p1)) ∧ True)) → (p3 ∨ (p4 ∧ True))) ∨ ((p3 → True) → ((True → True) → (False → (p3 ∨ p2))))) := by
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
theorem thm_5_vars_158685066633610611273201555508 : ((p2 ∧ ((((p1 ∧ (p4 ∨ p1)) → p4) ∨ p3) ∨ (p3 ∧ ((False ∨ p2) → (p5 ∨ (p1 ∨ p4)))))) ∨ ((False → False) ∧ (p5 → (False → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228087235841164963971464826970 : ((p4 ∧ (False ∨ False)) ∨ ((p3 ∨ p1) → (((((((p5 → True) → True) ∧ p2) ∧ (True → p5)) ∧ (p4 ∨ p1)) ∧ p2) → (p3 ∨ (True ∨ p4))))) := by
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
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h7.left
  let h10 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h12 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h15 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137816378619371975582003526874 : ((p3 ∨ (((((p4 ∧ (True → False)) ∨ p3) ∨ (((p4 ∨ ((p1 ∨ p3) ∧ True)) ∧ p2) → p3)) ∧ (p4 ∧ p3)) ∨ True)) ∨ ((p4 → p5) ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670260207722141770297450350912 : (((((((True → p1) ∨ p3) → p1) → ((((p2 ∨ p2) ∨ p4) ∧ p2) ∨ (p1 ∧ ((p5 → (p3 ∨ False)) ∨ p1)))) ∨ (True → (True ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53827010766813346501513674873 : (((((False ∨ ((p4 ∨ p2) → True)) ∨ p4) → (p2 → p1)) ∨ ((((False ∨ p1) ∧ False) ∨ (p3 ∨ ((False ∨ p4) ∨ p5))) → (False ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318653573275502444827982975225 : (p4 ∨ ((p2 → ((((((True → p1) ∧ ((False ∨ (p5 ∨ p1)) ∧ p2)) ∧ ((p3 ∧ p4) → p1)) ∨ (p1 ∧ p4)) → p3) ∨ p4)) ∨ (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190348494201268743896743025544 : ((((p3 ∨ (p1 → p3)) ∨ ((p4 ∨ p3) ∧ p2)) ∨ True) ∨ ((((False ∧ (p2 ∧ (p5 → p3))) ∧ p5) ∧ p4) ∨ (p1 → (p5 → (p2 → p5))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_751046909144341684708562255275 : (((True ∧ ((p4 → ((p5 → False) ∧ p2)) ∧ ((((False ∨ False) ∨ p1) ∨ p5) ∨ (((p1 ∨ (((True ∨ False) → p2) ∧ p5)) ∧ p2) → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191308879518361211382609530758 : (((p4 → p1) ∧ (((False ∨ p4) → p2) → (p1 ∨ False))) ∨ (p3 → ((p4 → ((p4 → (p4 ∨ (p5 → (p4 ∨ p5)))) ∨ p4)) ∨ (p5 ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_793380263657643439216274610586 : (((True → (p5 ∧ ((p4 → (False → (p5 ∧ (p4 ∨ (p4 ∨ (((p1 → True) ∨ p5) ∧ (((p3 ∨ p5) → (p2 → p3)) ∧ p3))))))) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184627685068715312981958803248 : (((True ∧ (p3 ∨ (True ∧ (p5 ∧ p2)))) ∧ ((p4 ∧ p1) ∧ p3)) ∨ ((p3 ∧ (True ∨ p3)) ∨ ((p3 ∧ (p5 → True)) → ((p4 ∨ True) → True)))) := by
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
theorem thm_5_vars_358607756234798034133388473930 : (p5 → (p3 → (((p3 → p4) ∧ (True → (p2 ∧ p1))) → (p5 → ((((p4 ∨ (p2 ∨ (p4 ∧ p3))) ∧ p4) → p1) ∨ ((p5 → True) ∧ p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h7
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118259774804416078580501658745 : ((p1 ∨ ((p3 → ((p1 ∧ ((True → p2) → (p5 ∨ (False → (p5 ∧ p1))))) ∨ p2)) ∨ (p3 → (p2 ∨ ((p1 ∨ False) ∨ p5))))) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_798358613567178545432425833686 : (((p1 → ((False → (((p2 → p4) ∧ p2) ∨ ((((p4 ∨ False) → p4) → p2) → True))) → ((False → p3) → ((False ∧ p3) ∨ (p1 ∨ p2))))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336722184927394723606898689604 : (p1 → (((((p3 → (p1 ∨ p2)) ∧ p2) ∨ p5) ∧ ((p2 → False) ∧ (True → (p3 → (p3 → (p1 ∧ ((False ∧ p3) ∨ (p5 ∧ False)))))))) → p5)) := by
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
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h4.left
    let h9 := h4.right
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h10 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h11 := h8 h10
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h4.left
    let h14 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319382893283067003280496923873 : (p4 ∨ ((True → ((((p2 ∧ p1) ∨ ((p3 ∧ True) ∧ p5)) ∧ (p3 ∧ False)) ∨ True)) ∨ (p1 ∨ ((((p4 ∧ True) ∨ p3) → p4) ∨ (p3 → p2))))) := by
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
theorem thm_5_vars_47550395857646526992580782026 : (((True → (((((p2 ∧ p1) → (True ∨ (p3 ∧ ((p1 ∧ (False → p3)) ∧ (True → (False ∨ p4)))))) → False) ∨ p3) ∨ p1)) ∨ (False → True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337077469493918729658447508174 : (p1 → (((True ∧ ((((False ∨ p3) ∧ ((True ∧ p3) ∧ (p3 ∨ p3))) ∧ (p3 → (p2 → False))) ∨ True)) ∧ ((True ∧ True) ∨ False)) ∨ (False → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111360520044983583515169434798 : (((p5 ∧ ((p1 → (p5 ∨ ((((p4 → p1) ∧ (False ∧ p1)) ∧ ((p5 ∨ (p2 → p3)) → True)) ∧ False))) ∧ (p2 → p3))) ∧ p2) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183398659683274666283271340346 : ((False ∨ (True ∧ (p3 ∨ ((p3 → True) → ((True ∨ False) ∨ p5))))) ∧ (p3 ∨ (p2 ∨ ((p1 → ((p2 ∧ False) ∨ ((p2 → False) → p1))) ∨ p1)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809282434490641439528996232297 : (((p5 → ((((p2 ∧ p5) ∧ p5) ∨ (((False ∨ (p3 → (True ∧ (p1 ∨ p4)))) ∧ p4) ∨ (((p3 ∨ (p1 → p3)) ∨ p4) ∧ True))) ∨ True)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_36633181039725130857545120026 : ((p5 → (((((p1 → (p2 ∧ (p1 → (((p1 ∨ p3) ∨ (p3 → True)) ∧ p1)))) → (False ∧ False)) ∧ (p3 → p2)) ∨ (True ∨ p4)) ∧ p5)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349943069861629478305342409738 : (p4 → (((((((p4 ∨ True) ∧ ((True → p3) ∧ p4)) ∧ ((p3 ∧ p2) ∧ (p1 ∨ ((True ∧ p1) → p2)))) ∧ (p3 ∧ p2)) → p5) ∧ False) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347112001292529428693200813249 : (p3 → ((((p1 ∨ p4) → False) → ((((True → (p5 ∨ p2)) ∨ p2) → p2) ∧ p3)) ∨ (p3 ∨ (((p1 → (p2 ∧ p1)) ∧ True) ∧ (p4 ∧ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217887944015093895750462951667 : (((p2 → (True ∨ p3)) → False) → (False ∧ (p1 → (((((p5 ∨ ((p4 ∧ p3) → (p3 → p5))) → p1) → p3) ∨ p1) → ((p3 ∧ p1) ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 → (True ∨ p3)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h8 : (p2 → (True ∨ p3)) := by
      -- Implications on the right can always be decomposed.
      intro h9
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h10 := h1 h8
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h12 : (p2 → (True ∨ p3)) := by
      -- Implications on the right can always be decomposed.
      intro h13
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h14 := h1 h12
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157626041104545601482613531498 : (((((p5 ∨ (p5 ∧ p5)) ∨ p2) ∧ (p4 ∨ (((p2 ∧ False) ∧ p3) ∧ p3))) ∧ ((False → p1) ∧ p4)) ∨ (False ∨ (p2 → ((True → False) ∨ True)))) := by
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
theorem thm_5_vars_720995487946625457598871690628 : (((((p2 → False) ∧ (p1 ∨ True)) → (p5 → ((p5 ∨ (p1 ∨ (p1 ∧ (p5 → True)))) → ((((p5 → (p2 ∨ p5)) ∨ p2) ∨ p5) ∨ p4)))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h1.left
    let h6 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h1.left
      let h12 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h14 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- Conjunctions on the left can always be decomposed.
      let h18 := h1.left
      let h19 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h20 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h21 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200437026734214575946563308738 : (((p4 ∨ False) ∨ (p1 ∧ ((p5 ∧ p3) → p1))) → (((p2 ∧ ((True → p2) ∧ ((((p5 ∧ p2) ∧ (p1 ∧ p2)) → p5) → p5))) ∨ p4) ∨ p1)) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h4 =>
      -- False on the left can always be used.
      apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185338080234036069049559170834 : ((p4 ∧ ((True ∨ (p3 ∨ ((False ∧ (p5 → p4)) ∨ False))) ∧ p3)) ∨ ((((p5 → (p1 ∨ p4)) → p4) ∨ p1) ∨ (p5 ∨ (p3 → (p1 → p1))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263408096697096068201859790539 : (True ∧ (((False ∨ (False ∨ False)) ∨ ((p2 ∨ (((p1 ∨ ((False ∨ p3) ∨ p2)) ∧ p5) ∧ ((p2 ∧ p3) ∧ p1))) → False)) ∨ (False → (p5 ∧ p4)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_47073921369611817863793849097 : ((((p2 → (True → (((p2 ∨ True) → p1) ∨ (p4 ∨ (p3 ∧ ((((False ∨ False) → False) ∧ False) ∧ p4)))))) ∨ (p3 ∧ p5)) ∨ (p4 ∨ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310074993571317121321901791339 : (p2 ∨ ((p2 ∨ (((p5 → p5) ∨ p1) ∨ (True ∨ ((p1 ∨ ((p5 → p4) → p5)) ∨ p4)))) → (((p2 ∨ (p1 ∨ False)) → p3) ∨ (True ∨ p1)))) := by
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
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Disjunctions on the left can always be decomposed.
          cases h10
          case inl h11 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h12 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43933285944434088969465933423 : ((((((p4 ∨ ((p1 ∧ False) → p3)) ∨ ((p5 → (p2 → p2)) → (False ∨ p5))) ∧ (p3 ∨ (p4 → (p2 → p3)))) ∨ (p2 ∨ p5)) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136343517676129226169519116430 : (((False ∨ (p2 → (p2 → p2))) ∧ (p5 → (((p4 ∧ (p1 ∨ (p4 → p2))) ∨ (((True → p3) → p2) ∨ True)) ∨ p1))) ∨ (p4 ∧ (p1 ∧ True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117143557956627306802429410686 : ((True ∧ ((((((((False → True) ∨ False) → p1) → ((p1 ∨ p4) ∧ p4)) → ((p4 ∧ False) ∧ (p2 ∧ p3))) → p3) ∧ p4) ∧ p1)) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174493491653154045671338653383 : ((((p1 ∧ ((p1 ∨ True) ∧ p1)) ∧ p4) ∨ (p1 → (p1 → (p4 ∧ (p4 → True))))) → (((((p2 ∧ p2) → p2) → (p2 ∧ True)) → p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151569557649759550095873381769 : ((((False ∧ (((p3 ∧ p1) ∨ p2) ∨ (((p5 → p2) → p4) ∧ (p4 → p5)))) ∧ (p3 → False)) → (p5 → p3)) → ((True → False) → (False ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206787330509802544970533503947 : ((p4 → (p3 ∧ ((p4 → p5) → p5))) ∨ (((p3 ∨ (((p3 → p2) ∨ False) ∧ p5)) → (p3 → p4)) → (p2 → (p5 → (p2 ∨ (p2 → p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226611389522115726251673019785 : (((p5 → p3) ∨ p4) ∨ (((True ∧ (p5 ∧ p3)) ∨ (p4 ∨ ((p2 ∧ (p3 → False)) → p2))) → ((p5 ∧ (p1 → (p4 → p4))) → (p3 ∨ True)))) := by
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
  cases h1
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785013051323908485510238579416 : (((p3 ∨ (p5 → (((p3 → (p1 ∧ (p2 ∨ (p4 → p4)))) ∨ (p3 → True)) → (p4 ∧ (((False → p2) ∧ (True → (p1 ∨ p1))) → p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42017452700519782986580007484 : ((((True ∧ False) ∨ (p1 ∧ (((((True ∧ False) ∧ (p3 → (False ∧ p3))) ∨ False) ∧ p5) ∨ (p2 → ((p2 ∧ p4) ∨ (False ∧ p2)))))) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_239175272723109062725973284739 : ((p2 ∨ True) ∧ (((p3 ∧ p3) → ((True ∧ p3) ∧ p4)) → (((p5 ∧ True) ∧ (p2 ∧ ((p2 → (p5 → ((p5 ∨ p1) → p3))) ∨ True))) ∨ True))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60100722674029224222475390804 : (((p3 ∨ p1) → ((p2 ∨ (True ∧ (p2 ∧ (p2 ∧ p2)))) ∨ (((((p1 ∨ p4) → ((False ∧ p2) → (p3 ∨ False))) → False) ∨ p2) ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197480762997013350221352187503 : ((((p2 ∧ p3) → (p2 → p4)) ∧ (p3 → True)) ∨ ((False ∧ ((p3 ∨ ((p2 → False) ∧ p1)) → ((p5 ∨ p4) ∨ (True → (p3 → p1))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111491201309082809568859907630 : (((p3 → ((p1 ∧ (p1 ∨ (p5 ∨ ((((p5 → p2) → p4) ∧ ((False ∧ False) → p4)) ∧ ((p4 → False) ∨ True))))) ∨ True)) ∧ p1) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64192640246696521850520700246 : ((False ∨ (True ∧ (p1 ∨ ((((p1 ∨ p4) → p1) ∧ True) → (p4 → (p2 ∨ (((True ∧ True) ∨ (((p3 → p1) → p5) ∨ p1)) ∧ p1))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65249287636645975093141124872 : ((p3 ∨ ((((((p2 ∧ (p5 → (p5 ∨ (False ∨ p3)))) ∧ False) ∨ p4) ∧ (p2 → ((True ∧ p5) → p1))) ∧ (p3 ∨ (p1 ∧ False))) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161558305729106052141189273640 : ((p5 ∧ (p4 ∨ (p1 ∧ ((p1 ∨ ((p1 ∧ (p4 ∨ p4)) → True)) ∨ (p4 → (p3 ∨ (p5 → False))))))) → ((True → p3) ∨ ((p1 ∨ p2) ∨ p5))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45932888440173093954494819360 : (((p4 → (p4 → (((((p5 → (p5 ∧ (p4 → (((p4 ∧ (p1 → p5)) → p3) ∧ False)))) → p3) ∨ False) ∨ (p3 ∨ p3)) → p5))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228166449205436680776242290691 : ((p5 ∧ (False ∧ p1)) ∨ (((((p3 → ((True → p3) ∨ (False ∨ p3))) ∧ p4) ∧ (p4 ∧ p2)) ∧ (((False ∨ p3) ∧ p3) → p3)) ∨ (False → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160690706190365189509335933689 : (((p2 ∧ ((((True ∨ p3) ∨ p5) ∧ p5) ∨ p3)) ∧ (p5 ∧ (((p3 ∧ p4) ∨ True) ∧ (p5 ∨ p4)))) → (p1 ∨ (p5 ∧ ((p1 ∧ False) → False)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h3.left
        let h12 := h3.right
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h15 =>
          -- Conjunctions on the left can always be decomposed.
          let h16 := h15.left
          let h17 := h15.right
          -- Disjunctions on the left can always be decomposed.
          cases h14
          case inl h18 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- One of the premise coincides with the conclusion.
            exact h18
            -- Implications on the right can always be decomposed.
            intro h19
            -- Conjunctions on the left can always be decomposed.
            let h20 := h19.left
            let h21 := h19.right
            -- False on the left can always be used.
            apply False.elim h21
          case inr h22 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- One of the premise coincides with the conclusion.
            exact h11
            -- Implications on the right can always be decomposed.
            intro h23
            -- Conjunctions on the left can always be decomposed.
            let h24 := h23.left
            let h25 := h23.right
            -- False on the left can always be used.
            apply False.elim h25
        case inr h26 =>
          -- Disjunctions on the left can always be decomposed.
          cases h14
          case inl h27 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- One of the premise coincides with the conclusion.
            exact h27
            -- Implications on the right can always be decomposed.
            intro h28
            -- Conjunctions on the left can always be decomposed.
            let h29 := h28.left
            let h30 := h28.right
            -- False on the left can always be used.
            apply False.elim h30
          case inr h31 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- One of the premise coincides with the conclusion.
            exact h11
            -- Implications on the right can always be decomposed.
            intro h32
            -- Conjunctions on the left can always be decomposed.
            let h33 := h32.left
            let h34 := h32.right
            -- False on the left can always be used.
            apply False.elim h34
      case inr h35 =>
        -- Conjunctions on the left can always be decomposed.
        let h36 := h3.left
        let h37 := h3.right
        -- Conjunctions on the left can always be decomposed.
        let h38 := h37.left
        let h39 := h37.right
        -- Disjunctions on the left can always be decomposed.
        cases h38
        case inl h40 =>
          -- Conjunctions on the left can always be decomposed.
          let h41 := h40.left
          let h42 := h40.right
          -- Disjunctions on the left can always be decomposed.
          cases h39
          case inl h43 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- One of the premise coincides with the conclusion.
            exact h43
            -- Implications on the right can always be decomposed.
            intro h44
            -- Conjunctions on the left can always be decomposed.
            let h45 := h44.left
            let h46 := h44.right
            -- False on the left can always be used.
            apply False.elim h46
          case inr h47 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- One of the premise coincides with the conclusion.
            exact h36
            -- Implications on the right can always be decomposed.
            intro h48
            -- Conjunctions on the left can always be decomposed.
            let h49 := h48.left
            let h50 := h48.right
            -- False on the left can always be used.
            apply False.elim h50
        case inr h51 =>
          -- Disjunctions on the left can always be decomposed.
          cases h39
          case inl h52 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- One of the premise coincides with the conclusion.
            exact h52
            -- Implications on the right can always be decomposed.
            intro h53
            -- Conjunctions on the left can always be decomposed.
            let h54 := h53.left
            let h55 := h53.right
            -- False on the left can always be used.
            apply False.elim h55
          case inr h56 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- One of the premise coincides with the conclusion.
            exact h36
            -- Implications on the right can always be decomposed.
            intro h57
            -- Conjunctions on the left can always be decomposed.
            let h58 := h57.left
            let h59 := h57.right
            -- False on the left can always be used.
            apply False.elim h59
    case inr h60 =>
      -- Conjunctions on the left can always be decomposed.
      let h61 := h3.left
      let h62 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h63 := h62.left
      let h64 := h62.right
      -- Disjunctions on the left can always be decomposed.
      cases h63
      case inl h65 =>
        -- Conjunctions on the left can always be decomposed.
        let h66 := h65.left
        let h67 := h65.right
        -- Disjunctions on the left can always be decomposed.
        cases h64
        case inl h68 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h68
          -- Implications on the right can always be decomposed.
          intro h69
          -- Conjunctions on the left can always be decomposed.
          let h70 := h69.left
          let h71 := h69.right
          -- False on the left can always be used.
          apply False.elim h71
        case inr h72 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h61
          -- Implications on the right can always be decomposed.
          intro h73
          -- Conjunctions on the left can always be decomposed.
          let h74 := h73.left
          let h75 := h73.right
          -- False on the left can always be used.
          apply False.elim h75
      case inr h76 =>
        -- Disjunctions on the left can always be decomposed.
        cases h64
        case inl h77 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h77
          -- Implications on the right can always be decomposed.
          intro h78
          -- Conjunctions on the left can always be decomposed.
          let h79 := h78.left
          let h80 := h78.right
          -- False on the left can always be used.
          apply False.elim h80
        case inr h81 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h61
          -- Implications on the right can always be decomposed.
          intro h82
          -- Conjunctions on the left can always be decomposed.
          let h83 := h82.left
          let h84 := h82.right
          -- False on the left can always be used.
          apply False.elim h84
  case inr h85 =>
    -- Conjunctions on the left can always be decomposed.
    let h86 := h3.left
    let h87 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h88 := h87.left
    let h89 := h87.right
    -- Disjunctions on the left can always be decomposed.
    cases h88
    case inl h90 =>
      -- Conjunctions on the left can always be decomposed.
      let h91 := h90.left
      let h92 := h90.right
      -- Disjunctions on the left can always be decomposed.
      cases h89
      case inl h93 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h93
        -- Implications on the right can always be decomposed.
        intro h94
        -- Conjunctions on the left can always be decomposed.
        let h95 := h94.left
        let h96 := h94.right
        -- False on the left can always be used.
        apply False.elim h96
      case inr h97 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h86
        -- Implications on the right can always be decomposed.
        intro h98
        -- Conjunctions on the left can always be decomposed.
        let h99 := h98.left
        let h100 := h98.right
        -- False on the left can always be used.
        apply False.elim h100
    case inr h101 =>
      -- Disjunctions on the left can always be decomposed.
      cases h89
      case inl h102 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h102
        -- Implications on the right can always be decomposed.
        intro h103
        -- Conjunctions on the left can always be decomposed.
        let h104 := h103.left
        let h105 := h103.right
        -- False on the left can always be used.
        apply False.elim h105
      case inr h106 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h86
        -- Implications on the right can always be decomposed.
        intro h107
        -- Conjunctions on the left can always be decomposed.
        let h108 := h107.left
        let h109 := h107.right
        -- False on the left can always be used.
        apply False.elim h109



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209083882929106889162210129084 : ((p2 ∨ (((p2 → False) ∨ False) ∧ p2)) → (p4 ∨ (p2 → (((p5 ∧ p5) → ((((p2 ∨ (True ∧ p3)) ∨ p5) → (p1 ∨ p1)) → p4)) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
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
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h8 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h9 := h7 h8
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_762943330669784088401395667968 : (((p3 ∧ ((False ∨ ((p4 ∧ False) ∧ p3)) ∧ (((False ∧ ((False ∨ ((False ∨ True) → (p1 → p1))) → (p1 → p2))) → (True ∧ True)) ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58508481341539527051620131111 : (((p4 ∨ p5) ∧ ((((((p3 → p5) ∨ (p1 ∨ True)) ∧ (((p1 ∧ p4) ∧ (False → True)) → p2)) → True) → p5) → (p5 → (False ∨ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727774325090244410283453729000 : ((((False ∨ (True → p1)) ∨ (((False ∨ (True → p2)) ∧ (p3 → (p3 → (False → ((True ∨ (p1 → True)) ∨ p1))))) → ((True → p1) ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115671636047239839392893377125 : ((((p2 ∨ p3) → (p5 ∨ (False ∧ True))) ∨ ((p4 → (p2 → ((((p1 ∨ (False → False)) → p3) → True) → (p1 ∨ p1)))) ∨ False)) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123581502037812411521780875312 : (((((p4 ∨ ((p3 ∨ p3) ∧ p4)) → (p4 ∧ p5)) → (p3 ∧ (False ∨ (p5 ∨ False)))) ∨ ((True → (p5 ∨ (p2 → p3))) → p1)) → (p1 → p1)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38893495388958039683428071406 : (((((True ∨ p1) → p1) ∨ (p5 ∨ (p3 ∧ (((p4 ∨ (p1 → p5)) → ((p2 → p2) ∨ (((p5 ∨ p4) ∨ False) ∧ True))) ∧ p4)))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133847021916559255935763578132 : (((True ∧ (p5 ∧ (((p4 ∧ p5) → ((p4 ∧ ((((p1 → False) ∧ p4) ∨ False) → (p3 ∨ p1))) → False)) → False))) ∧ False) ∨ ((p2 ∨ True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192691893366341427770589760332 : (((((p5 → p2) ∨ (p3 ∨ p4)) ∨ (False ∨ False)) → p1) → (p2 → ((p4 → ((p3 → (p4 → (p5 ∨ p1))) ∧ p3)) ∨ ((p3 → p2) ∧ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : (((p5 → p2) ∨ (p3 ∨ p4)) ∨ (False ∨ False)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h4
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337053443232437183437996306736 : (p1 → (((p3 ∧ (p3 ∨ (((p3 ∨ (p1 → p5)) ∨ ((p5 → (((True → (p4 ∧ p5)) ∧ p3) → p5)) ∨ True)) → p4))) ∨ p1) ∨ (p1 ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245325805472294777552505849835 : ((p2 ∧ p2) ∨ (p1 ∨ ((((p5 ∧ True) ∨ (((((p1 → True) ∧ (((p5 → p2) ∨ p1) ∨ p2)) → p1) → True) ∧ True)) → (False ∨ True)) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147136954715703690191087474484 : (((True ∧ ((True → (p5 → (True → p2))) ∨ ((p4 ∨ (p3 ∧ ((False → p3) ∧ p2))) ∨ (p4 ∧ p1)))) ∧ p1) ∨ ((p2 ∧ (False ∨ p2)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309921506539386413018643188179 : (p2 ∨ (((True → (((True ∨ p4) ∧ (p5 ∧ p3)) ∧ ((p5 → (p1 ∧ p4)) ∧ p1))) → (p2 ∧ False)) ∨ (((p1 ∧ True) → (p1 ∨ True)) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64774967023784126329761300883 : ((p2 ∨ ((((((p4 ∧ ((p2 ∧ p2) → p5)) ∧ (True → p2)) ∨ (((True → p4) → (p2 ∨ p1)) ∨ (p2 → p3))) → p3) ∨ True) ∨ p3)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609204483265206159032159809064 : (((((((False ∨ p3) → p2) ∧ ((p2 ∧ ((False ∧ p5) ∧ ((p2 ∧ p4) ∨ p3))) ∧ ((False ∧ True) ∧ ((p4 → p4) ∧ True)))) ∨ True) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_84793616562265290501313245738 : ((((True ∨ p4) → (((p4 ∨ True) ∨ (p5 ∧ ((p1 ∧ p4) ∧ False))) → p4)) ∧ (((p1 ∧ (((True ∨ False) ∨ False) ∨ p3)) ∨ p1) ∧ p2)) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h12 : (True ∨ p4) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h13 := h2 h12
          -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
          have h14 : ((p4 ∨ True) ∨ (p5 ∧ ((p1 ∧ p4) ∧ False))) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h13, we can now drive its conclusion.
          let h15 := h13 h14
          -- One of the premise coincides with the conclusion.
          exact h15
        case inr h16 =>
          -- False on the left can always be used.
          apply False.elim h16
      case inr h17 =>
        -- False on the left can always be used.
        apply False.elim h17
    case inr h18 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h19 : (True ∨ p4) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h20 := h2 h19
      -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
      have h21 : ((p4 ∨ True) ∨ (p5 ∧ ((p1 ∧ p4) ∧ False))) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h20, we can now drive its conclusion.
      let h22 := h20 h21
      -- One of the premise coincides with the conclusion.
      exact h22
  case inr h23 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h24 : (True ∨ p4) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h25 := h2 h24
    -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
    have h26 : ((p4 ∨ True) ∨ (p5 ∧ ((p1 ∧ p4) ∧ False))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h25, we can now drive its conclusion.
    let h27 := h25 h26
    -- One of the premise coincides with the conclusion.
    exact h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345364575007678087933241179232 : (p3 → ((((((p4 → (True → (False → True))) ∨ (p1 ∧ p4)) → ((False ∨ True) ∧ ((p5 → False) → (True → True)))) → (p2 ∧ p5)) ∨ p3) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343532549336184822616695574682 : (p2 → ((True ∨ True) → (((True → ((p1 ∧ p3) → p4)) ∧ (p2 ∧ (((p1 ∨ ((p4 ∨ p4) ∨ (p1 ∨ p4))) → (False ∨ False)) ∧ p3))) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_325649125423613370466271470369 : (p5 ∨ (False ∨ (True ∧ ((p5 → (p1 → (p1 ∧ p5))) ∧ (((False ∨ p1) ∧ p5) → ((p5 ∧ ((p4 ∧ ((p2 → p2) ∧ p4)) ∨ p4)) ∨ p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300149726280249624076426183057 : (False ∨ ((p1 ∨ ((False → p4) → (((p2 → ((p4 ∨ (p4 ∨ p1)) ∧ ((p2 ∨ p5) ∨ p1))) ∨ p5) → ((p1 ∨ p1) ∨ p1)))) ∨ (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785959012400088757151814931129 : (((p4 ∨ ((((((p2 ∧ p3) → False) → ((p1 ∨ p4) → p3)) ∨ ((p1 ∧ ((p3 → p5) ∨ True)) ∨ True)) ∧ (p4 ∨ True)) ∨ (p1 → p5))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67324999259140149148295450374 : ((p1 → ((((True ∧ ((p1 ∨ True) ∧ (False ∨ (p3 → (p2 → ((((p1 ∨ True) → False) ∧ p5) ∨ (True ∧ p2))))))) ∧ p4) ∨ False) ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178088146509789680333982812393 : (((((p5 ∨ (p1 → p3)) → (((p3 ∧ True) ∧ p5) ∨ p5)) → p3) → p2) ∨ (((True → p3) → ((True → (p2 ∨ (False → p5))) ∨ p1)) ∨ p1)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_650998770421124046622058629579 : ((((((True → ((True → p4) ∧ False)) → p3) → (p1 ∨ (((p2 ∨ ((True → p4) ∨ p2)) ∨ p3) ∨ (p4 ∨ (p3 → p1))))) ∧ (p4 → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174150157634325802053742867856 : ((((((False → True) ∧ p1) → ((p2 → True) ∨ p5)) ∨ (True ∨ True)) ∨ (p4 → p5)) → ((((p3 → p3) → False) ∨ ((True → True) ∨ p2)) ∨ p4)) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h4
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h7
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h9
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h10 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h11
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217078655247037229932152012251 : ((((p5 → p4) ∧ p3) ∨ True) → (p2 ∨ (((p5 ∨ ((p4 → p2) ∨ (((p2 ∨ p2) ∧ True) ∧ p1))) ∨ (p2 ∨ p4)) → ((p1 → p5) ∨ True)))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h10 =>
          -- Conjunctions on the left can always be decomposed.
          let h11 := h10.left
          let h12 := h10.right
          -- Conjunctions on the left can always be decomposed.
          let h13 := h11.left
          let h14 := h11.right
          -- Disjunctions on the left can always be decomposed.
          cases h13
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h20 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h21
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h22 =>
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h23 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h24 =>
        -- Disjunctions on the left can always be decomposed.
        cases h24
        case inl h25 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h26 =>
          -- Conjunctions on the left can always be decomposed.
          let h27 := h26.left
          let h28 := h26.right
          -- Conjunctions on the left can always be decomposed.
          let h29 := h27.left
          let h30 := h27.right
          -- Disjunctions on the left can always be decomposed.
          cases h29
          case inl h31 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h32 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
    case inr h33 =>
      -- Disjunctions on the left can always be decomposed.
      cases h33
      case inl h34 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h35 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174374790396830953500549134051 : (((((p3 → (p5 → p1)) ∧ (p4 ∧ p5)) ∨ p1) ∧ (p1 → ((p2 ∨ p3) → p2))) → (p1 ∨ ((((p2 ∧ p3) ∧ False) → p5) → (p5 ∨ True)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h10 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_914749468147554720017755706407 : (((((p1 ∨ True) ∧ (True → (((((p4 ∧ p3) ∧ p3) → p2) → p2) → (True ∧ p5)))) ∧ (p2 ∧ ((p1 → p3) → (p1 → (p4 ∨ p5))))) → p5) ∧ True) := by
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
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h3.left
    let h8 := h3.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h10 := h5 h9
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h11 : ((((p4 ∧ p3) ∧ p3) → p2) → p2) := by
      -- Implications on the right can always be decomposed.
      intro h12
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h13 := h10 h11
    -- We need to get the right conjuct of h13 based on <expert-advice>.
    let h14 := h13.right
    -- One of the premise coincides with the conclusion.
    exact h14
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h3.left
    let h17 := h3.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h18 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h19 := h5 h18
    -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
    have h20 : ((((p4 ∧ p3) ∧ p3) → p2) → p2) := by
      -- Implications on the right can always be decomposed.
      intro h21
      -- One of the premise coincides with the conclusion.
      exact h16
    -- We have shown the premise of h19, we can now drive its conclusion.
    let h22 := h19 h20
    -- We need to get the right conjuct of h22 based on <expert-advice>.
    let h23 := h22.right
    -- One of the premise coincides with the conclusion.
    exact h23
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158202474475752155563076919228 : ((((p5 ∧ True) ∨ p5) ∧ (p5 ∧ (((p1 → (p5 → True)) → (p2 → p3)) → (p3 → (p1 → p5))))) ∨ ((((p5 → False) ∧ False) → False) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_769685579197488536367937674998 : (((p5 ∧ (p1 ∨ (((((False ∧ p5) → p3) → (((((p2 → p5) ∨ ((True ∨ p2) ∧ (p1 ∨ p2))) ∨ p3) ∨ p4) → p5)) ∨ p5) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185484638804185764359143319458 : ((p1 ∨ (p3 → (p1 → (((True → (p5 ∨ p3)) → p3) → p5)))) ∨ ((p1 ∧ (p5 ∨ p4)) ∨ (((False → p3) ∨ p5) ∧ ((False → p4) ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49183589499274777931644606117 : ((((p5 → (p1 ∧ (True → p4))) ∨ ((((p4 → p2) ∧ p3) ∨ ((p1 → ((p2 ∨ p5) ∨ p2)) → False)) ∨ p2)) ∨ (p2 → (p2 ∨ p2))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119264645084877054815728406665 : ((p2 → (p3 → (((True → False) ∧ (p4 ∨ ((p2 → ((p2 ∧ (False ∧ (p1 ∨ p3))) ∧ (p4 ∨ p2))) ∧ p2))) ∨ (True ∨ p3)))) ∨ (p2 → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166150338268341740325133488843 : ((False ∧ (((p4 ∨ ((p2 → p5) ∨ (((p1 ∧ p5) ∨ False) ∧ p2))) ∧ (True → p1)) ∨ p3)) ∨ (p2 → ((p2 ∨ False) ∨ (False ∨ (p3 ∨ True))))) := by
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
theorem thm_5_vars_49915146999763575262479780880 : (((((((((p1 ∧ False) ∧ True) ∧ p5) → p2) ∧ ((p3 ∧ False) ∧ (p1 ∨ False))) → (True ∧ p1)) → p3) ∧ (False ∧ ((p1 ∨ p2) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61189005998984490498646992910 : ((False ∧ ((p3 → p5) ∧ (True ∧ (((True → True) → p3) ∧ ((((p5 ∧ p1) → p2) ∧ (p2 → ((False → False) → False))) ∨ (True ∨ p1)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305769766817612856770866066100 : (p1 ∨ ((((p2 ∨ p4) → (True → p1)) ∨ (p3 ∨ p3)) ∨ ((p1 ∨ ((p3 ∧ (p5 ∨ (p2 ∧ ((p1 → p1) → p5)))) ∨ p2)) → (True ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h11 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172940336033169766212790231855 : ((p3 ∧ ((p5 ∧ ((False → p5) ∧ p3)) ∨ (False ∧ ((p5 ∧ True) ∨ (p4 ∨ p1))))) ∨ (((p2 → (False ∧ (p3 → p5))) ∨ False) → (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123653428271377578912715835567 : ((((((True ∨ True) ∧ ((p1 → p2) ∨ (p1 ∧ False))) ∨ p3) → ((p2 ∨ False) ∨ True)) → ((p1 ∧ p4) ∧ ((p5 → False) ∧ p5))) → (p1 ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((True ∨ True) ∧ ((p1 → p2) ∨ (p1 ∧ False))) ∨ p3) → ((p2 ∨ False) ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
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
          -- Conjunctions on the left can always be decomposed.
          let h10 := h9.left
          let h11 := h9.right
          -- False on the left can always be used.
          apply False.elim h11
      case inr h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h14 =>
          -- Conjunctions on the left can always be decomposed.
          let h15 := h14.left
          let h16 := h14.right
          -- False on the left can always be used.
          apply False.elim h16
    case inr h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h18 := h1 h2
  -- We need to get the left conjuct of h18 based on <expert-advice>.
  let h19 := h18.left
  -- We need to get the left conjuct of h19 based on <expert-advice>.
  let h20 := h19.left
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656252273664661959499214193984 : (((((((((p5 → True) → (p2 → (False ∨ p3))) ∨ p1) ∨ p5) ∨ True) ∧ (p5 → (p4 ∨ (False ∨ (p1 ∧ (True ∧ p5)))))) ∨ (False → False)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193501470077986090524151347010 : (((p4 ∨ p1) ∨ ((((False ∨ True) ∨ False) ∨ p3) ∨ p5)) → ((((((p2 ∨ p2) → False) → (False ∨ True)) → p2) ∧ p1) → (p3 ∨ (p3 → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h8 : (((p2 ∨ p2) → False) → (False ∨ True)) := by
        -- Implications on the right can always be decomposed.
        intro h9
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h10 := h3 h8
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h13 : (((p2 ∨ p2) → False) → (False ∨ True)) := by
        -- Implications on the right can always be decomposed.
        intro h14
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h15 := h3 h13
      -- One of the premise coincides with the conclusion.
      exact h15
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
          -- Disjunctions on the left can always be decomposed.
          cases h19
          case inl h20 =>
            -- False on the left can always be used.
            apply False.elim h20
          case inr h21 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h22
            -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
            have h23 : (((p2 ∨ p2) → False) → (False ∨ True)) := by
              -- Implications on the right can always be decomposed.
              intro h24
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h3, we can now drive its conclusion.
            let h25 := h3 h23
            -- One of the premise coincides with the conclusion.
            exact h25
        case inr h26 =>
          -- False on the left can always be used.
          apply False.elim h26
      case inr h27 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h27
    case inr h28 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h29
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h30 : (((p2 ∨ p2) → False) → (False ∨ True)) := by
        -- Implications on the right can always be decomposed.
        intro h31
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h32 := h3 h30
      -- One of the premise coincides with the conclusion.
      exact h32



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789054957839329215604639732558 : (((p5 ∨ ((p2 ∨ ((((False ∨ (p5 ∨ (p3 ∨ ((False ∧ (False ∧ p1)) ∧ ((False → p2) ∨ True))))) ∧ p3) → p2) ∨ p4)) → (False ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258507698634816053286872831118 : ((p5 ∨ p2) → (p5 ∨ ((((p1 → p3) ∨ (p4 ∨ p1)) → p5) ∨ (((((True → True) ∧ ((p3 ∨ True) ∨ p2)) ∨ p5) → True) ∨ (False → p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_649343281393677989932568896883 : (((((p5 ∨ (p2 ∧ (((((((p4 → (((p4 → p2) ∨ p3) → p5)) → p1) ∧ True) ∨ False) → p1) → p5) → p4))) → p1) ∧ (False ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67453333447811988922658197666 : ((p1 → ((((p2 ∧ ((p1 → p1) → True)) → ((p1 ∧ p3) ∧ (p2 ∨ False))) ∨ ((p3 ∨ p4) ∨ p1)) ∧ ((False → p1) → (p1 → p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



