variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336438631885746206780950991041 : (p1 → ((p3 ∨ (p1 ∧ (p2 ∨ ((((p4 → True) → (False ∨ p1)) → (p5 ∨ True)) ∧ (p5 → ((p4 → ((p2 ∨ p1) ∧ False)) ∨ p2)))))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789118068870960309511981176170 : (((p5 ∨ (((p4 → (((p2 ∧ (((p5 ∧ (False → p4)) → p4) ∨ ((p5 ∧ p1) ∨ p3))) ∧ p2) → p5)) ∨ p5) ∨ (p5 → (False ∨ True)))) ∨ p1) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_170587527071966559031354252543 : (((p2 → True) ∨ (p4 ∧ (((p3 ∧ (p4 ∨ (p5 ∧ (p2 → p1)))) ∨ p2) ∨ p2))) ∧ ((((((p1 → p4) ∨ p1) ∨ p2) → p3) ∧ True) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354832344209576297590124638220 : (p5 → (((False ∧ p1) ∧ ((((((p3 → ((p2 → False) → True)) ∨ (True ∧ (True → True))) → p4) ∧ True) → True) → (p3 → (p2 → p1)))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199337355272733131936685520276 : (((((p5 ∨ p1) ∧ (p1 ∧ False)) → p5) ∨ False) → (((p4 ∧ p3) ∧ (p4 → ((p3 ∨ p4) → p5))) ∨ (True ∨ (p5 → ((True ∨ p3) ∨ False))))) := by
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
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322835017676910619181756152746 : (p5 ∨ (((((False ∧ (False → False)) → (True ∨ False)) ∧ (p2 ∨ True)) ∧ (((True ∧ (p1 ∨ True)) ∨ (p5 ∧ (False ∨ p1))) → (False ∧ False))) → p5)) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h7 : ((True ∧ (p1 ∨ True)) ∨ (p5 ∧ (False ∨ p1))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h8 := h3 h7
    -- We need to get the left conjuct of h8 based on <expert-advice>.
    let h9 := h8.left
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h11 : ((True ∧ (p1 ∨ True)) ∨ (p5 ∧ (False ∨ p1))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h12 := h3 h11
    -- We need to get the left conjuct of h12 based on <expert-advice>.
    let h13 := h12.left
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_803926576417760014130919414239 : (((p3 → ((p2 ∧ ((((p4 → (p4 → (p3 → (p1 → (p5 ∨ ((p2 ∨ True) ∨ p5)))))) ∧ p2) → (p5 ∧ p2)) → False)) → (p5 ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57729243276515655356597032582 : ((((p2 ∨ False) → p4) → (((((False ∧ p5) ∨ (((False ∧ p5) ∨ p3) → ((False ∧ p1) ∨ (p2 → p5)))) ∨ p4) ∨ (True ∨ p3)) ∨ p1)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_756086562486380418003487506912 : (((p1 ∧ ((p1 → (False → (p1 ∨ (p4 → (True ∨ (p2 ∧ (((p1 → True) → ((p1 ∧ (p3 → p5)) ∨ (p2 → False))) → p4))))))) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158222924804322827167812218892 : (((True ∨ (p5 ∧ p4)) ∧ (p2 ∨ (((p4 ∨ (False ∨ p1)) ∨ (p4 → p2)) → (p1 ∨ (p2 ∧ True))))) ∨ (p4 ∨ ((p2 → True) ∨ (False ∧ p3)))) := by
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
theorem thm_5_vars_345680417446907301816372907800 : (p3 → ((p2 ∨ (p5 → ((((False ∨ p4) ∧ (p3 → p1)) ∧ ((p1 ∨ ((True ∧ (p4 ∧ p2)) → p4)) → p2)) ∨ (p1 → (False ∨ p3))))) ∨ p4)) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_673127158215502525788478278480 : (((((((p3 ∨ ((p2 ∨ p5) ∨ (p1 ∧ p1))) ∧ p3) ∧ (True → p4)) → (p2 → (p2 ∨ ((p3 ∨ True) ∧ p2)))) → (p5 ∨ (p3 → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174844847562827668270232913825 : (((False ∨ True) ∨ ((((p4 ∧ True) ∧ False) ∨ ((False → p5) ∧ (p3 ∧ p1))) → p2)) → ((False ∨ (p1 ∧ p4)) ∨ (True ∨ ((False ∧ p4) ∧ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- False on the left can always be used.
      apply False.elim h3
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_104675390892418899370910862084 : (((p1 ∨ ((((False ∨ p3) ∧ (p3 → True)) → (p1 ∨ (p5 ∧ True))) → (p5 → (p3 ∧ ((False ∧ p4) ∧ True))))) ∨ (p4 ∨ True)) ∧ (p3 ∨ True)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166430454670376696127445667753 : ((p1 ∨ (p2 ∧ (p3 ∨ ((p3 ∧ p2) ∨ (((((False ∧ p5) → False) ∧ p2) ∨ True) ∨ p1))))) ∨ (((False ∨ False) ∧ p5) → ((p3 ∧ p5) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198036561284878780498450736227 : (((False ∧ p5) ∨ (p3 ∧ (p5 ∨ (True ∧ p5)))) ∨ ((False → ((False → ((((p3 ∨ (True ∨ p3)) ∨ p1) ∨ True) → True)) ∧ p4)) ∧ (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_804733774907391395643922645636 : (((p3 → (((p4 ∧ True) → p2) ∨ (False ∧ (False ∧ (((False ∨ True) ∨ (((p5 ∧ False) ∧ p1) ∨ (p1 → p3))) → (True ∨ (p5 ∧ True))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_760412897225827600652988209 : (((p4 → (True → True)) → ((True ∧ p5) ∨ ((p5 ∨ ((True ∧ (p5 ∨ False)) ∨ ((False ∧ (p4 → False)) ∧ (True ∧ False)))) ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614839335679630718393623576466 : (((((p1 ∨ ((p1 ∨ p2) → (p3 ∧ (True ∧ (((((p1 ∧ p1) → p4) ∨ p3) ∨ p1) → p3))))) ∨ ((p1 ∧ p5) ∧ (p1 ∧ p2))) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_39528795037900971387319143740 : (((False ∨ ((p3 ∧ ((((p1 ∧ p5) ∨ p1) ∨ ((p5 ∨ p4) → p4)) ∨ False)) ∨ ((p2 → (False → p4)) ∨ ((p1 ∨ p4) ∨ p5)))) ∧ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44909330021104312287846557805 : ((((False → (False ∨ p2)) → (((p5 ∧ ((p3 → (p4 ∨ False)) ∧ p5)) ∧ False) ∧ ((p3 ∧ (((p5 ∧ p5) ∨ False) ∧ False)) → p4))) → p3) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → (False ∨ p2)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64810229310753419955984944555 : ((p2 ∨ (((((True ∨ (p2 ∧ (p5 ∨ ((p2 → (False → True)) ∨ ((((p5 → False) → p5) ∧ p5) → p1))))) → p1) ∨ p3) ∧ p4) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185351327607453903297308146220 : ((p4 ∧ (((True ∧ p4) ∧ p4) ∨ ((True → p3) ∧ (p4 ∨ p4)))) ∨ (p1 → (p1 ∨ (False ∧ (p4 ∨ (p2 → ((False ∨ (p2 ∨ p1)) → False))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679756016963853020442817884122 : (((((((p4 → (False ∧ ((p3 ∧ p4) → p1))) ∧ True) ∨ (True ∨ ((True ∧ (False → p3)) ∨ p5))) ∨ p3) → ((p4 ∨ (False ∧ p1)) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314464097271562334858563655312 : (p3 ∨ ((((((True → (False ∨ p1)) ∨ (True → p5)) → False) → ((False ∨ p4) → p4)) ∧ (p2 → (True → p5))) → ((p3 → p2) ∨ (False → p3)))) := by
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60441800770305744870240691076 : (((p5 → True) → (((((p1 → p4) → (p2 → ((p1 → p5) → p1))) → (p1 → (p2 ∧ (((True → p1) → False) ∧ p3)))) → True) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60474326586564222744459273891 : (((p5 → p4) → (p5 → (((p1 ∧ p4) ∨ (p1 ∧ (p5 ∧ ((p4 ∨ p4) → p1)))) ∧ ((p2 → ((False ∨ p4) ∨ p4)) → (p1 ∧ True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110989344034590860739243708015 : ((((p1 ∨ ((False → p5) ∨ ((p4 → p2) → (p3 ∧ ((((p1 ∨ p4) → p4) ∨ (p3 ∧ p5)) ∧ p3))))) → (p4 ∨ p2)) ∧ p4) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57081537137159463497528803214 : ((((False ∧ p5) ∧ p3) ∨ (((p2 ∨ (False ∨ False)) → ((((p1 → p1) ∧ ((p3 ∧ (p5 → True)) ∧ (p2 ∨ p1))) → p1) → p1)) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246107892063089144162460959366 : ((p4 ∧ p1) ∨ ((p5 → True) → ((True ∨ p4) ∧ ((((p5 ∧ p5) ∨ True) → ((p1 ∨ (p4 ∨ True)) → False)) ∨ (True ∨ (p1 ∧ (True ∨ p2))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_800353418815607365316965549689 : (((p2 → (((p3 ∧ (p4 ∨ p4)) ∧ (p5 ∧ ((p1 ∧ ((False ∧ p1) ∨ True)) → ((p1 ∧ ((p2 ∧ (p5 → True)) ∧ p3)) ∧ p3)))) ∨ p2)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677174207910583621329227311763 : (((((((p2 ∧ (((p1 ∨ p1) → p4) ∧ (False ∧ (p5 ∧ p1)))) ∨ ((False ∧ p3) ∧ p3)) ∨ p3) ∧ p4) ∨ (p2 ∨ ((p4 ∨ True) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_942818513788749102440460639212 : (((((p5 → (p5 ∨ p2)) → False) ∧ ((p3 → (p1 ∨ ((p1 → ((True ∧ True) ∧ ((p1 ∧ p5) → ((p3 ∧ p2) → True)))) ∧ False))) → p4)) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p5 → (p5 ∨ p2)) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40217746849500636153720058768 : (((((True → p1) → (((((False ∧ p3) → False) → (((p3 → p1) ∨ p4) → (((False ∨ p2) → p1) ∨ p4))) → p3) → p5)) ∧ p4) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57086744386136879588147071532 : ((((p2 ∧ p1) ∧ p2) ∨ (((False ∨ p2) ∧ True) ∨ (True → ((False ∧ p1) → ((((p4 ∨ p1) ∨ (p2 → (p1 ∨ p2))) ∨ True) → False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64928540109417346977386292094 : ((p2 ∨ (((p5 ∨ (True → (((False ∧ ((True ∧ p4) → p2)) → p4) ∧ p5))) ∧ False) ∨ (p4 → (p4 → (p1 → (p5 ∧ (False → p5))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749902960337600951701377443732 : (((True ∧ ((((((p5 ∨ ((p5 → (True ∨ p2)) → p3)) ∨ ((p5 ∧ (p1 → p1)) ∧ ((p5 ∨ False) ∨ p4))) ∨ True) ∨ p4) ∨ False) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_210468267498057235897705317129 : (((p1 → (p2 ∧ False)) ∨ True) ∧ (p1 → (p2 ∨ (((p4 ∨ (p2 ∧ (p4 ∧ ((((False ∧ p5) → False) ∨ True) ∨ True)))) ∧ (p5 ∧ p4)) ∨ True)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228196830634195650908598204637 : ((p5 ∧ (p5 ∧ p4)) ∨ (((p2 ∧ (False ∨ (((p2 ∧ (p1 → p2)) → True) → True))) ∧ (((True ∨ (p3 ∨ (p2 ∨ True))) ∧ p1) ∨ True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196151505413521014976884286827 : ((True ∨ (p1 ∨ (((p3 ∨ p1) ∨ p4) ∨ p2))) ∧ (((False → p4) → (False ∧ (p3 → False))) → (p2 ∧ (False ∨ ((p3 ∨ (p3 ∨ p1)) → False))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → p4) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- False on the left can always be used.
  apply False.elim h5
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : (False → p4) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h6
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353375413793035037585964537970 : (p4 → (False ∨ ((((True ∨ True) ∧ p1) ∨ ((p4 ∧ p1) → p5)) ∨ (((p5 → p4) ∧ (((p3 ∨ p5) → (p2 → p5)) → (False ∧ p5))) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_647185406769619137491684075491 : ((((p3 → (p2 ∨ (((False ∧ p3) ∨ (p5 ∨ (p4 ∨ (True → (((p2 → ((p5 → False) ∧ p5)) → p1) ∨ p1))))) ∧ (p4 ∨ True)))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_733885176456300940168614229251 : ((((p5 ∧ p5) ∧ (p4 ∧ (((((p2 ∧ p2) ∧ p3) ∧ (((((False ∨ p1) ∨ (False ∧ p3)) → p2) ∧ p2) ∨ (p2 ∨ p4))) ∨ p5) ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215783063871324748096817456082 : ((p1 ∨ (p1 ∧ (p5 ∨ p4))) ∨ ((p5 ∨ ((p2 → (p2 ∧ p2)) → True)) ∨ (((p1 ∨ (p3 ∨ ((p2 ∧ p4) ∨ (p4 → p3)))) → False) ∧ p4))) := by
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
theorem thm_5_vars_48994314082205345177993298030 : ((((p5 ∧ (((True → (((((False ∨ ((True ∨ p1) → p5)) → True) ∨ p5) ∨ p4) ∨ p5)) ∨ p1) → False)) ∨ p1) ∨ (False → (True ∨ p4))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345384663029449339316384199378 : (p3 → (((p2 ∨ ((((p1 ∧ False) ∧ ((p2 ∧ True) ∧ p5)) → (((p3 → True) ∧ ((False → p4) ∨ (True ∨ p1))) ∧ p5)) → False)) ∨ p2) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613852500012401176017915040876 : ((((((p4 ∨ ((p3 ∨ False) ∧ ((((False ∨ (p4 ∨ (p3 → True))) → False) ∨ (p5 ∨ p2)) ∧ p4))) ∧ p5) ∨ (p3 → (p3 ∨ True))) ∨ p1) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_503940973492080096309911490 : (((((((False ∧ (p1 ∧ True)) → (p1 → p1)) ∧ (p1 ∨ (False → p2))) → p4) ∧ (((p1 ∧ (True → p3)) → p2) → p2)) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111009997177084164730854564561 : (((((p5 ∧ (True ∧ (((p1 ∨ (False ∨ p5)) ∨ p1) → (False → p3)))) ∧ (True → (p4 ∨ p1))) ∨ ((p4 ∨ p4) → False)) ∧ p5) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_674494090687106812517400113640 : ((((p4 ∨ (True ∧ ((p2 ∨ (((p3 → (p4 → p5)) ∧ ((p2 ∧ p1) ∧ p4)) ∧ p2)) → ((True → p2) ∨ False)))) → (p4 ∧ (p1 ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112896549164045324175124183922 : ((((p2 → True) ∧ (p2 ∧ (p5 ∧ ((p5 ∨ (((((p4 ∨ (p2 → p2)) ∧ p1) ∨ p3) ∧ p1) ∨ (False ∨ p4))) ∧ p4)))) → p3) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_636003963522647693582087044510 : (((((((((False ∨ (p1 ∧ p1)) ∧ False) → p3) ∧ p4) → (((p4 ∨ p5) → p5) → True)) ∧ ((p3 ∧ (p4 → (p4 ∧ p2))) ∧ p2)) → p3) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  let h6 := h4.left
  let h7 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301797549972494524479735186570 : (False ∨ ((p4 ∧ p1) ∨ ((((p2 ∨ (p3 ∨ (((True ∧ p5) → p4) ∨ p2))) ∨ (False ∧ (p1 ∧ (False ∨ (p4 → True))))) ∧ p3) → (False ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
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
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148846220780239640479914574553 : ((((p5 ∧ p2) ∧ (p5 ∨ p2)) ∧ ((p1 → (p1 ∨ p4)) → (((p3 ∨ (p1 → p2)) ∧ (p1 ∧ p1)) ∨ p1))) ∨ ((p1 → p2) ∨ (False → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301145097700035680808535020976 : (False ∨ (((((p3 → p2) ∨ p2) → p5) ∧ (False ∨ p1)) ∨ ((p3 ∧ (True → (False ∧ False))) → (((p3 ∨ (p5 ∨ p1)) ∨ (p1 ∧ True)) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_496582491425808449280954762 : (((((p1 ∨ p5) → ((p1 ∨ ((p2 ∨ (((p4 → p3) ∧ ((p2 ∧ p3) → p1)) ∨ p5)) ∨ p5)) → (True ∧ p5))) → False) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707901422529911293211492467818 : ((((p4 ∧ ((p3 ∧ p5) ∨ (False ∧ (False ∨ p5)))) ∨ (True ∧ ((p1 → (False ∧ ((p4 ∨ p1) ∧ (False → False)))) → (p3 → (True → True))))) ∨ p2) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_628277689658333216510713622190 : ((((((p3 → p3) ∨ (p2 ∧ (((p2 ∨ (((p5 ∨ ((True → p1) ∨ (p4 ∧ p5))) ∨ (p1 → p1)) ∧ p4)) ∨ p2) → True))) ∧ p2) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233313624688179653306803445422 : ((True ∨ (p5 ∨ p3)) → (False ∨ (((p5 ∨ p5) ∨ (False → p3)) ∧ ((True ∧ (p4 ∨ (((False → p5) ∨ (p1 ∨ p4)) ∧ p4))) ∨ (p3 → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- False on the left can always be used.
      apply False.elim h9
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48570141418974014465293431029 : (((((True ∧ True) → (((((p3 ∨ (p5 → True)) ∨ (False ∧ p2)) ∧ p4) ∨ p2) → (True → (p3 → False)))) → False) ∧ ((False ∨ p1) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148461698329963740645568631105 : (((((p4 ∨ False) ∧ True) ∧ (((p1 → (p2 ∧ False)) → p1) ∨ p4)) ∧ (((p2 ∨ (p4 ∨ False)) ∧ p4) ∨ p5)) ∨ ((p4 ∨ p5) → (True ∨ True))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50420204948047413083586264947 : (((p3 ∧ (((((p3 ∧ (p1 ∨ p1)) → (((p5 ∨ p3) ∧ p2) ∨ (p2 ∨ p1))) ∨ True) → p2) ∧ False)) ∨ (True ∧ (p2 ∨ (p3 → p3)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118594422698950548306770157127 : ((p4 ∨ ((((False ∨ (((p5 ∧ True) ∨ p4) → False)) ∧ (False ∨ (((p4 ∧ p4) ∨ p5) → p2))) ∨ (False ∨ p3)) ∧ (p3 ∧ p4))) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219070408481542521427836277133 : ((p5 ∧ (p3 ∨ (p3 ∨ p4))) → ((((((p1 ∨ (p2 ∨ False)) ∨ (((True ∨ p1) → p5) ∧ p3)) ∨ p3) → ((p2 → p4) → p4)) ∨ p3) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h8
      -- Implications on the right can always be decomposed.
      intro h9
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Disjunctions on the left can always be decomposed.
          cases h11
          case inl h12 =>
            -- One of the premise coincides with the conclusion.
            exact h7
          case inr h13 =>
            -- Disjunctions on the left can always be decomposed.
            cases h13
            case inl h14 =>
              -- One of the premise coincides with the conclusion.
              exact h7
            case inr h15 =>
              -- False on the left can always be used.
              apply False.elim h15
        case inr h16 =>
          -- Conjunctions on the left can always be decomposed.
          let h17 := h16.left
          let h18 := h16.right
          -- One of the premise coincides with the conclusion.
          exact h7
      case inr h19 =>
        -- One of the premise coincides with the conclusion.
        exact h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_735095249630942878602839858545 : ((((p3 ∨ p1) ∧ ((((False → (p3 → True)) ∧ (p3 → True)) ∨ p4) → (((p2 ∧ p5) ∧ ((p2 ∨ (p5 ∧ p5)) ∧ (p4 → p4))) ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38497975594207729350007861660 : (((((p4 ∨ ((p5 ∨ ((p1 ∨ p1) ∧ p4)) ∨ (p1 → p2))) → False) ∨ (p3 ∨ ((p1 → p1) → ((False → False) ∧ (p1 ∨ True))))) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_818821075525126876651764519764 : ((((((p2 ∧ ((False ∧ ((p4 ∨ p4) → p3)) ∨ (p4 → ((p5 ∧ p5) ∧ (p2 ∨ ((p3 ∨ p5) ∨ p4)))))) → p1) → (p1 ∧ p5)) ∧ p1) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p2 ∧ ((False ∧ ((p4 ∨ p4) → p3)) ∨ (p4 → ((p5 ∧ p5) ∧ (p2 ∨ ((p3 ∨ p5) ∨ p4)))))) → p1) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- False on the left can always be used.
      apply False.elim h9
    case inr h11 =>
      -- One of the premise coincides with the conclusion.
      exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h12 := h2 h4
  -- We need to get the right conjuct of h12 based on <expert-advice>.
  let h13 := h12.right
  -- One of the premise coincides with the conclusion.
  exact h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_640608225287397328324825762531 : (((((p1 ∨ False) ∧ (p5 → ((((p1 → ((p3 ∨ p3) → (p4 ∨ (p1 ∧ p5)))) ∨ p2) ∧ p5) ∨ (((p1 → p2) ∨ p1) ∨ True)))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179373305104047501428986574472 : ((p2 ∨ (p4 ∧ (p1 ∨ (((p1 → (p2 → p3)) ∧ p2) ∨ (p2 ∨ p2))))) ∨ ((False → (p3 ∨ p5)) ∨ (((p3 ∨ (False ∧ p3)) ∧ p2) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142084250697374072752740743640 : ((True ∧ ((p4 → p5) ∧ ((p1 ∧ ((p1 ∨ p5) ∨ (True → p4))) → (((p4 ∨ p2) ∧ p1) → ((True ∧ p3) ∨ p1))))) → ((p3 → p4) ∨ True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_335704474910550788886477442951 : (p1 → (((((p5 → p1) ∧ p4) → (((p5 ∨ ((p5 ∧ (p5 ∨ (True → (p1 → True)))) ∨ p3)) ∨ (p2 ∧ p5)) → (True ∧ p3))) ∨ True) ∧ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780190420972766293134696992185 : (((p2 ∨ (((p4 ∨ ((p2 ∨ ((p3 ∨ (p3 → p2)) → True)) ∧ (p3 ∧ (True → (p1 → (p1 ∧ p3)))))) ∨ p2) ∨ (p5 → (False ∨ p5)))) ∨ False) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346771866292279862517501179202 : (p3 → ((((True ∨ (p2 ∨ ((p3 ∧ p1) ∧ ((p5 ∨ (p1 ∧ True)) → p3)))) ∨ (p3 ∨ (p1 ∧ p3))) → p5) ∨ (p1 → ((p3 → p1) ∨ True)))) := by
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
theorem thm_5_vars_41316560726433641757795179707 : (((((((p4 ∨ False) ∨ p5) ∧ (True → p2)) ∨ ((((p4 ∨ p2) ∨ p5) ∧ p5) ∨ p4)) ∧ (p1 → ((p4 ∧ (True ∨ False)) ∨ True))) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262240241889484385071949550384 : (True ∧ ((((p4 ∨ ((False ∨ p5) ∨ ((((False ∨ True) ∨ p5) → (((False → p5) → p3) ∧ False)) ∨ True))) ∧ (p1 → p2)) → (p2 ∨ p3)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_805369415525910190746050408918 : (((p3 → (False ∨ (((((False → p4) ∨ p5) → ((p5 ∨ False) ∨ p1)) ∨ (p4 ∧ False)) ∧ (False ∨ (True → (False ∧ ((True ∨ p5) ∧ p5))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622722051222731825620865880172 : ((((p4 ∧ ((p2 ∧ p2) ∨ (p2 ∨ (p5 ∨ ((((p5 ∧ False) ∧ ((True ∨ p4) → p2)) → p2) → (False ∨ ((p1 ∧ p3) ∨ False))))))) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_114686756599500076118002442826 : (((p5 ∨ (p2 → ((True → (False ∨ ((True ∧ p2) → ((p1 → p3) → p3)))) → p1))) ∨ (p1 ∨ (((p4 → True) → p2) ∨ p5))) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110981334720857410705954279200 : ((((((p3 → (((True → True) → p5) ∧ True)) ∨ (p5 ∧ p2)) → ((p1 ∧ p3) → ((True ∧ p5) ∨ p1))) → (True ∧ p1)) ∧ p4) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611991113766768678972941726633 : ((((((p2 ∧ ((p4 ∨ (p1 ∧ False)) ∨ ((p1 ∧ (p5 ∨ ((p2 ∧ p2) ∧ False))) ∨ ((True → p1) → p5)))) ∨ p5) ∧ (p4 ∧ p3)) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_562810949622912561873686624877 : (((p5 ∨ ((p3 → (p5 ∨ (((((p1 ∨ (p1 ∧ p3)) → p3) → (p3 ∨ True)) ∨ p4) → p5))) ∨ ((False ∨ (p5 ∧ (True ∨ False))) ∨ True))) ∧ True) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137210247596064067715708824687 : ((False ∧ (p2 → (p2 ∧ (p2 ∧ (((p2 → p3) ∧ True) → (((((True ∨ p3) ∧ p5) ∧ p3) ∧ (p4 ∨ p2)) → p1)))))) ∨ ((False → p1) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689661058963803642278131555973 : ((((((p4 → (p3 ∧ p5)) ∧ p3) ∨ ((False ∨ p3) → ((p5 ∨ (p4 ∧ p1)) ∨ p5))) ∨ (((True ∧ (True ∧ p4)) → (p3 ∧ p4)) ∨ True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_633223548418152807366412762195 : (((((True → (((((True ∧ ((p1 ∨ False) ∧ (p2 ∨ (p1 ∨ p4)))) ∧ p2) ∧ p2) ∨ p4) ∧ ((False ∧ p3) ∨ p5))) ∧ (p2 → p2)) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179375204895306424180631987298 : ((p2 ∨ (p2 ∨ ((((False ∧ (False ∨ p1)) ∧ p3) → (p2 → p5)) → p5))) ∨ ((((p4 ∧ ((p1 ∧ p4) → p4)) ∧ False) → (True ∧ False)) ∨ p3)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_162026134410748986802403240194 : ((p4 → (((p1 → p3) ∨ (p4 ∧ (p1 ∨ ((p1 ∧ p5) ∧ (p5 → p2))))) ∨ (True ∧ (p2 → p5)))) → ((p4 ∧ p2) → (p3 ∨ (True ∧ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38629307449861126709342313742 : ((((((p4 ∧ p1) ∨ p2) ∧ ((p4 → p5) ∧ p2)) ∨ (p4 ∨ ((p2 → (((True ∧ p1) ∧ (p3 ∨ p1)) → True)) ∧ (p5 → p5)))) ∧ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340958723932639612652649110450 : (p2 → ((((True ∨ p3) → p3) → ((False ∧ (p3 → p4)) ∨ ((p2 ∨ (((True → p5) → (p2 ∧ p1)) ∨ ((p2 → False) → p2))) → p3))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352884339677214281972591476940 : (p4 → (True ∧ ((p4 ∧ (True ∧ ((((p2 → (p1 ∨ p5)) → (p5 → p2)) → p5) → (p3 ∨ False)))) ∨ (True ∨ ((p2 → (p5 ∨ p3)) ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185190175417460080907661911343 : ((True ∧ ((((p3 ∨ p5) ∧ True) ∧ (False ∧ (p2 → p5))) ∨ p1)) ∨ (p5 → (((((False → p3) ∨ p1) → True) ∨ ((p5 ∧ p2) → p5)) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314413110455239038948816649772 : (p3 ∨ (((p4 → (p1 ∨ (p5 ∧ ((((False ∧ (True ∨ (p2 ∨ p3))) ∧ p3) ∨ (True → True)) → p5)))) → p2) ∨ (p4 ∨ (True ∨ (p1 → p2))))) := by
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
theorem thm_5_vars_352559995405708040909769938277 : (p4 → ((p2 ∨ True) ∧ (p2 → (p2 → ((((p5 ∧ (p3 ∨ (p4 → (((False → (p5 → (p4 ∧ p5))) → p5) ∨ p1)))) → False) ∧ p5) ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149032148938037595440014058672 : (((False ∧ (True → p3)) ∨ (((((p2 ∧ (p2 ∧ p1)) ∧ (p2 ∧ p2)) ∧ (p1 → (p1 → p3))) ∨ True) ∨ p1)) ∨ (p4 ∨ (p2 ∨ (p3 ∨ p4)))) := by
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
theorem thm_5_vars_686598264700414697072706207216 : (((((p5 ∧ True) ∨ (((p5 ∨ False) ∨ (p3 ∨ (True ∧ ((p5 ∧ (p1 ∨ p2)) → p5)))) ∨ p5)) → (False ∨ ((p3 → p5) ∨ (False ∧ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204526910755928564013014506849 : (((((p3 ∨ True) ∨ p1) → p3) ∨ p1) ∨ (False ∨ (((p5 → ((p2 → (False ∨ (p4 ∧ True))) → False)) ∨ (p2 ∨ p2)) ∨ ((p1 ∧ False) → True)))) := by
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
theorem thm_5_vars_319917363931018589828787136031 : (p4 ∨ (((True → False) ∧ (p4 → False)) → (p3 ∧ (p2 ∧ ((((p5 ∨ ((((p2 ∧ p4) ∧ p5) ∨ (True → p5)) ∧ True)) ∧ True) ∨ p5) → p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h9 := h6 h8
  -- False on the left can always be used.
  apply False.elim h9
  -- Implications on the right can always be decomposed.
  intro h10
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h1.left
      let h16 := h1.right
      -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
      have h17 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h15, we can now drive its conclusion.
      let h18 := h15 h17
      -- False on the left can always be used.
      apply False.elim h18
    case inr h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h19.left
      let h21 := h19.right
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h22 =>
        -- Conjunctions on the left can always be decomposed.
        let h23 := h22.left
        let h24 := h22.right
        -- Conjunctions on the left can always be decomposed.
        let h25 := h23.left
        let h26 := h23.right
        -- Conjunctions on the left can always be decomposed.
        let h27 := h1.left
        let h28 := h1.right
        -- We want to use the implication h28 based on <expert-advice>. So we show its premise.
        have h29 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h26
        -- We have shown the premise of h28, we can now drive its conclusion.
        let h30 := h28 h29
        -- False on the left can always be used.
        apply False.elim h30
      case inr h31 =>
        -- Conjunctions on the left can always be decomposed.
        let h32 := h1.left
        let h33 := h1.right
        -- We want to use the implication h32 based on <expert-advice>. So we show its premise.
        have h34 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h32, we can now drive its conclusion.
        let h35 := h32 h34
        -- False on the left can always be used.
        apply False.elim h35
  case inr h36 =>
    -- Conjunctions on the left can always be decomposed.
    let h37 := h1.left
    let h38 := h1.right
    -- We want to use the implication h37 based on <expert-advice>. So we show its premise.
    have h39 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h37, we can now drive its conclusion.
    let h40 := h37 h39
    -- False on the left can always be used.
    apply False.elim h40



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234585960569419974279611204172 : ((p3 → (False ∨ p5)) → ((p2 → True) → (p5 ∨ ((((False ∨ p4) → (p1 ∨ p1)) ∧ (p4 ∧ (p5 ∧ p5))) ∨ ((p2 ∧ (p3 → p4)) → p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111758779900820293844997037055 : ((((((((True ∧ (False ∨ p1)) → ((p2 ∧ False) ∧ (p5 ∧ (p5 → p4)))) → p5) → (True → p4)) → p4) ∧ (True → False)) ∨ True) ∨ (p2 ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60957994917315968615353696584 : ((False ∧ ((((((p4 ∨ ((True → p1) ∨ p5)) ∧ p3) → ((True ∨ False) ∧ p4)) ∧ ((p3 → p4) ∨ (False ∧ True))) → (p1 → p2)) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171887929647193826483503072812 : (((p1 ∨ ((p1 ∧ (p4 ∧ (p3 → p1))) → (((True ∨ p2) ∧ False) ∧ p1))) → p3) ∨ (((((False ∨ (p4 ∨ p4)) ∧ p5) → p4) ∨ False) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h7
  -- True on the right can always be proven directly.
  apply True.intro



