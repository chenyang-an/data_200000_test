variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146963772964220711375939786350 : (((((((p4 → (p1 ∨ ((False → ((p1 → p5) ∨ p1)) ∨ (p2 ∧ False)))) ∧ p4) → True) ∧ p5) → p3) ∧ True) ∨ ((True ∨ False) ∨ (p1 ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55570473417598767209177249325 : (((True ∨ ((False ∧ p3) → (p3 ∨ True))) → (p2 ∧ ((p4 ∨ p4) → ((((p4 ∨ ((p4 ∨ p3) ∧ False)) → p4) ∧ p3) ∧ (False ∨ p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56237808854883366756946896891 : (((p5 ∨ (True ∧ (p1 ∨ p2))) ∨ ((p1 → p5) ∧ (((False ∧ (p3 ∧ False)) ∧ (p2 ∨ ((p3 ∧ ((False ∧ True) ∨ True)) ∧ p3))) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209179251248090607153949955730 : ((p4 ∨ ((p3 ∧ (False → True)) ∧ False)) → (((True ∨ (((True → True) ∨ (p5 ∨ (True ∧ (p2 ∨ p4)))) ∨ (False → (p1 ∨ p2)))) → p5) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53296343304909099997367526513 : (((p2 ∨ ((((True → p5) ∧ ((p1 ∨ p3) ∧ p4)) ∨ False) ∨ p1)) ∨ (True → (p5 → (p4 → ((((True ∧ p4) ∨ p1) ∨ p5) → True))))) ∨ p3) := by
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
theorem thm_5_vars_742368558443270377646734506478 : ((((p1 → p4) ∨ (((((p2 → True) ∧ (False ∧ ((p5 ∧ p3) ∨ ((p1 → p4) → False)))) ∨ ((p5 ∧ p1) ∨ p4)) ∨ False) ∨ (True → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39969668883642000887332924696 : (((p4 → ((p1 ∨ False) ∨ (((p5 → (False ∨ (False → ((False ∧ (p1 ∧ (p2 ∧ ((True ∧ False) ∧ p4)))) ∨ p5)))) → p5) ∧ p3))) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111163862181300600071081903704 : ((((((p1 ∨ p5) ∨ p1) → True) ∧ ((p4 ∨ p4) ∨ ((((False → (p5 ∨ p2)) ∧ (p3 → (p4 ∨ p5))) ∧ True) ∧ p2))) ∧ p4) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299328099829103594020077096137 : (False ∨ (((((p3 ∧ p2) ∧ p3) ∨ p2) ∨ (False → ((p5 ∧ (p2 ∧ True)) → ((p2 → (((p2 → p2) ∨ p2) ∨ p2)) → (p2 → p3))))) ∨ p3)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_582781506735988823742035230583 : (((p5 → (((p1 → p1) → (False ∨ (((((p5 ∧ p2) → (p3 ∨ (p1 → p5))) ∧ (True → p5)) → p2) ∨ ((p3 → p4) ∧ p1)))) ∨ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_661359848046595781875577628521 : (((((((p3 ∨ p3) → (p3 ∧ p3)) ∨ (False ∧ ((True ∨ (True ∧ False)) ∨ ((p1 → (p3 ∨ p4)) ∧ p1)))) → (p5 ∧ p4)) → (False ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207661552502310063095667957838 : ((((p4 ∧ p5) ∨ (p1 ∧ p1)) → p5) → (((((p2 ∨ p4) → (False ∧ (p4 ∧ False))) ∨ p5) → p4) ∨ (((False ∨ True) ∨ (p3 ∨ p2)) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_596303791357710435532424382029 : (((((((p5 ∧ (p5 ∨ p1)) ∧ (False ∨ False)) ∧ False) ∨ (True ∧ (p1 → ((p1 ∧ p4) ∧ (p2 ∨ (((True → p3) ∨ p5) ∧ p5)))))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309745779208801950117769142652 : (p2 ∨ (((p1 ∨ ((((False ∨ (p5 ∧ p2)) ∧ p2) ∧ ((p4 ∨ p5) ∧ p5)) ∨ (True ∨ p5))) ∨ (p3 → p1)) ∧ (p5 ∨ (p4 → (p3 ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59480851002411314324906230004 : (((p1 → p3) ∨ (((p5 → ((((((p4 ∨ p1) → p1) ∧ (False → p4)) ∨ (p1 → p1)) → True) → True)) → (p4 ∧ False)) ∨ (p1 → True))) ∨ p5) := by
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
theorem thm_5_vars_612639032300989715906947643329 : ((((((((False ∧ p5) ∨ ((p1 ∧ ((True → p5) ∨ p1)) → ((True ∧ p2) ∨ p1))) ∨ p3) ∧ ((p4 → p5) ∧ p4)) ∨ (p4 → p5)) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_348819227696485835336132328712 : (p3 → (p1 ∨ (((False ∨ p4) ∨ p4) → ((False ∧ p1) ∨ (((p5 ∨ p2) → (p5 → (((p3 → ((p3 ∨ p4) → p4)) ∧ False) → p4))) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_734141292062451463141304333673 : ((((True ∨ p5) ∧ (((p5 ∨ (p5 ∨ ((p2 ∨ (True ∨ p3)) ∨ p1))) → (((p1 ∨ (p4 ∨ p5)) ∨ p1) ∨ (False ∧ p4))) ∧ (True ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160377103266061163723613887781 : (((((p3 → p5) ∧ False) → ((p4 ∨ (((p5 ∧ p4) → p5) ∧ p2)) → p5)) ∧ ((p2 ∧ p4) ∨ p5)) → ((p5 ∧ (p4 → (False ∨ p2))) ∨ True)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156982784496373754640888173775 : (((((p5 → p4) ∨ (False → (True → (p3 ∧ False)))) → (((p4 ∧ (p5 ∨ p5)) ∨ False) ∧ p5)) ∨ False) ∨ ((False ∧ p4) → (False ∨ (p5 ∧ p4)))) := by
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
theorem thm_5_vars_635579577037262045371029990745 : (((((((p3 ∧ ((p4 → p4) ∧ (True ∧ p3))) → (p3 ∧ False)) ∧ ((p2 → (p3 ∨ False)) ∧ p3)) ∨ (p1 → ((p3 ∧ p5) ∧ True))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49041802918695920728057877589 : ((((p4 ∨ (p2 ∧ ((False ∧ ((True ∧ p3) ∧ ((((p3 → p5) → p3) → True) ∨ (p5 → True)))) → p5))) → False) ∨ (False → (True ∨ True))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117406679257252219106528052978 : ((p1 ∧ (((((False → (((p3 ∧ p3) ∧ p5) ∨ p2)) ∧ p5) → (p5 ∧ p1)) → (False ∨ (((False ∧ p1) ∧ p3) ∧ p3))) → p3)) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47430744251271178807877676004 : (((p2 ∧ (((p1 ∨ p4) ∧ (((p1 → (p1 ∨ p3)) ∧ ((p3 ∧ p3) ∨ False)) ∨ (((True ∨ p1) ∧ True) ∨ p2))) → p4)) ∨ (False ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693774352017382826984283731416 : ((((((((p4 ∧ True) ∨ ((True ∨ p4) ∨ p2)) → (p1 → p4)) ∨ False) → p4) ∨ (p1 ∨ ((p4 → (p4 → p1)) ∧ ((True ∨ p1) ∧ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190069020264114580471449959749 : (((((p3 ∧ p1) ∧ (p1 → (True ∨ True))) → p5) ∧ False) ∨ (((p1 → True) ∨ p5) ∧ (((((p2 → p1) ∨ p5) ∨ (p1 ∧ p4)) → p1) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_133900215002956317444786271899 : (((p1 ∨ ((True → (False ∧ (True ∨ ((p5 ∨ ((p5 ∧ True) → (True → (p5 → p1)))) → p4)))) ∨ (p3 ∨ True))) ∧ p1) ∨ (p2 ∨ (p2 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699600344742478317532307867212 : (((((((p1 ∨ p1) ∧ ((p3 ∧ (p2 → True)) ∨ p2)) → p5) → p3) → (((p5 ∧ (False ∨ p5)) ∨ (p2 ∧ p4)) ∧ (p2 ∨ (True ∨ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167628037861086357840435524668 : (((((p4 ∨ False) ∧ (((p3 ∧ p2) ∧ ((True ∨ p3) ∨ p2)) → p5)) → False) → (p3 ∧ p2)) → ((p5 → ((p4 ∨ False) ∨ (False ∧ p1))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216813984929832267813713176792 : (((p2 ∧ (p4 → p1)) ∧ True) → ((((((p5 ∧ p1) ∨ p2) ∨ p1) → (p4 ∨ (p1 ∧ ((p1 ∨ (p3 ∨ p3)) → False)))) ∨ (p3 → p2)) ∧ p2)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h7.left
  let h10 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_722827108424305520007211610666 : (((((False ∧ p3) ∨ p3) ∧ (p4 → ((p5 → (p2 ∨ False)) ∨ (True ∧ (((True ∨ p1) → p5) → ((((p4 → p3) ∨ p1) ∨ p4) ∨ False)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136630417526763407005041541041 : ((((True ∨ False) ∨ p3) → (False ∨ ((p1 → (((p1 → p3) ∧ (p3 ∧ p4)) ∧ p5)) ∧ ((p5 ∨ p2) → (p3 ∧ p4))))) ∨ (p3 → (p5 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347117251564648845835189008617 : (p3 → ((p3 ∧ (p4 → ((False ∧ p4) ∨ (p2 ∨ (p5 ∧ ((p3 ∧ p1) ∨ p2)))))) ∨ (p3 ∨ (((p1 ∧ (True → p2)) ∧ (True ∧ p4)) ∧ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45877478482324532043650454161 : (((p3 → (((True → p5) ∨ (True ∨ p2)) ∧ (((((p1 ∨ p2) ∨ (((p3 → (p5 ∧ True)) ∧ p2) ∧ False)) ∧ p3) → p1) ∧ True))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_93934598321417850388450441949 : ((p1 ∧ (((p2 → (p2 → p4)) ∨ p4) ∧ ((((p4 ∧ (p3 ∨ p1)) → False) ∧ ((p1 → p1) ∧ (p4 ∧ (p4 ∨ False)))) ∧ (p5 → p1)))) → p5) := by
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
    let h7 := h5.left
    let h8 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h16 : (p4 ∧ (p3 ∨ p1)) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h15
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h17 := h9 h16
      -- False on the left can always be used.
      apply False.elim h17
    case inr h18 =>
      -- False on the left can always be used.
      apply False.elim h18
  case inr h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h5.left
    let h21 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h22 := h20.left
    let h23 := h20.right
    -- Conjunctions on the left can always be decomposed.
    let h24 := h23.left
    let h25 := h23.right
    -- Conjunctions on the left can always be decomposed.
    let h26 := h25.left
    let h27 := h25.right
    -- Disjunctions on the left can always be decomposed.
    cases h27
    case inl h28 =>
      -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
      have h29 : (p4 ∧ (p3 ∨ p1)) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h28
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h22, we can now drive its conclusion.
      let h30 := h22 h29
      -- False on the left can always be used.
      apply False.elim h30
    case inr h31 =>
      -- False on the left can always be used.
      apply False.elim h31



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342176903140299276404219131061 : (p2 → ((False ∨ (((p2 ∨ p4) → (p3 ∧ (p3 ∧ False))) ∨ ((p1 ∧ (False ∨ False)) ∨ ((p4 ∨ p5) ∧ p2)))) ∨ (((True ∨ p5) ∨ p1) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57807382634214158195220993750 : (((p2 ∧ (p2 ∨ p3)) → ((p4 ∧ ((p4 ∨ p3) → (p1 ∨ ((p3 → ((((p1 → p3) ∧ p2) ∨ p3) ∧ True)) ∨ p3)))) ∨ (p1 ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179098657959687132611538092548 : ((False ∧ ((((p1 ∨ False) → p5) ∨ (p4 ∧ (p5 ∨ p4))) → (p1 ∨ p5))) ∨ (True → ((p1 → p1) ∨ (True ∨ ((p2 ∨ p4) ∧ (True ∧ True)))))) := by
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
theorem thm_5_vars_213923895461094956090497854184 : (((True → (True → p2)) ∨ p3) ∨ (((((p2 ∧ ((True → True) ∧ True)) ∧ ((True ∨ (False ∧ True)) → ((False → p2) ∧ p1))) ∧ p5) → p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47301194418139834369187968516 : ((((p1 ∨ (p2 ∨ p1)) ∧ ((False ∨ (((False ∧ (False → p1)) → (p4 ∨ p4)) ∧ False)) ∧ ((p5 → p2) ∨ (False ∧ False)))) ∨ (p2 ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165373333092526368587330819787 : (((((p1 ∨ (p2 ∨ p5)) → ((p5 ∨ True) → (p5 → p3))) → p3) ∨ ((p2 ∨ p3) ∨ True)) ∨ ((((p3 → p2) → (True → p1)) → False) ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731100152236778075593707423971 : ((((p1 ∨ (p1 → p3)) → ((p3 ∨ (p1 ∨ ((((((p1 → p5) ∧ p4) ∨ p4) ∨ p2) ∧ p1) ∨ p1))) ∨ ((True ∨ p2) ∧ (p1 → p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186103625068731741839113684529 : (((((True ∧ p3) ∧ ((False → p5) ∨ p5)) ∨ (p5 ∨ p2)) ∨ p5) → ((p2 ∧ p3) ∨ ((False ∨ p5) → (p1 ∨ (p1 ∨ (False → (p3 → False))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Conjunctions on the left can always be decomposed.
      let h4 := h3.left
      let h5 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h6 := h4.left
      let h7 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h9
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- False on the left can always be used.
          apply False.elim h10
        case inr h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h12
          -- Implications on the right can always be decomposed.
          intro h13
          -- False on the left can always be used.
          apply False.elim h12
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h15
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h16 =>
          -- False on the left can always be used.
          apply False.elim h16
        case inr h17 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h18
          -- Implications on the right can always be decomposed.
          intro h19
          -- False on the left can always be used.
          apply False.elim h18
    case inr h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h21 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h22
        -- Disjunctions on the left can always be decomposed.
        cases h22
        case inl h23 =>
          -- False on the left can always be used.
          apply False.elim h23
        case inr h24 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h25
          -- Implications on the right can always be decomposed.
          intro h26
          -- False on the left can always be used.
          apply False.elim h25
      case inr h27 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h28
        -- Disjunctions on the left can always be decomposed.
        cases h28
        case inl h29 =>
          -- False on the left can always be used.
          apply False.elim h29
        case inr h30 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h31
          -- Implications on the right can always be decomposed.
          intro h32
          -- False on the left can always be used.
          apply False.elim h31
  case inr h33 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h34
    -- Disjunctions on the left can always be decomposed.
    cases h34
    case inl h35 =>
      -- False on the left can always be used.
      apply False.elim h35
    case inr h36 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h37
      -- Implications on the right can always be decomposed.
      intro h38
      -- False on the left can always be used.
      apply False.elim h37



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158937696757601907509249085146 : ((p2 ∨ ((False ∨ ((True ∧ (p1 ∧ ((False ∨ p4) → True))) → (((p3 ∨ True) → True) ∨ p1))) → p1)) ∨ (((False → False) ∧ False) → (p5 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134027880059138288084721460678 : (((((p1 ∧ (p1 ∧ (p1 → (True ∨ (p5 ∨ ((((p3 ∨ p2) → True) → True) → (False ∨ False))))))) → p5) ∨ False) ∨ p2) ∨ (True → (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136537811494136109173379207307 : (((p5 → (False ∨ True)) ∧ (((p3 ∧ p3) ∧ ((False ∨ (False ∨ p3)) → ((p2 ∨ (True → p5)) ∨ p1))) ∨ (p2 → p3))) ∨ (p1 ∨ (False → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177909772899101943097720300477 : (((((False ∨ p4) ∨ ((p4 ∨ False) ∨ (p4 ∧ p4))) → (False ∨ p5)) ∨ p2) ∨ ((((True ∨ p3) → ((False → p1) → False)) ∨ p4) → (p1 → p1))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234724037333024153205571493900 : ((p4 → (p4 ∨ p2)) → (((p5 ∧ p3) → p5) ∧ ((True → p5) → ((((p1 → (p4 ∨ (p3 → p4))) ∨ True) → p3) → (p5 ∨ (p5 ∧ False)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h7 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h8 := h5 h7
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215793442363537707458175880028 : ((p1 ∨ (p1 ∨ (p4 ∧ False))) ∨ (((((p4 ∨ p5) ∧ p1) ∨ p4) ∨ True) ∧ ((p2 → (False ∨ (True ∧ True))) ∨ (True ∨ (p1 ∨ (True ∨ p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225102757919119283414052563296 : (((p2 ∧ p1) ∧ p2) ∨ (((True ∧ (((p5 ∨ p3) → p3) → (((p1 ∧ p3) ∧ False) → p5))) → p4) ∨ ((p4 ∧ p4) → ((p3 ∨ True) ∨ False)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161312275261623874503219145335 : ((True ∧ (((((p5 ∨ p3) ∨ True) ∧ p2) ∧ (p2 → (((True → p3) → p1) ∧ False))) ∧ (p5 ∨ p4))) → (((False ∧ p2) ∨ p2) ∧ (p5 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h19 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9
  -- Implications on the right can always be decomposed.
  intro h20
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351850151909902324231725057032 : (p4 → ((((p2 ∨ (p1 ∨ False)) ∨ False) ∨ (p2 ∨ ((False ∧ True) ∨ p2))) → ((p3 ∨ (p5 ∨ p2)) → (((False → p5) ∨ False) → (p5 ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h2
      case inl h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- Disjunctions on the left can always be decomposed.
          cases h8
          case inl h9 =>
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
              -- False on the left can always be used.
              apply False.elim h12
        case inr h13 =>
          -- False on the left can always be used.
          apply False.elim h13
      case inr h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h16 =>
          -- Disjunctions on the left can always be decomposed.
          cases h16
          case inl h17 =>
            -- Conjunctions on the left can always be decomposed.
            let h18 := h17.left
            let h19 := h17.right
            -- False on the left can always be used.
            apply False.elim h18
          case inr h20 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
    case inr h21 =>
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h22 =>
        -- Disjunctions on the left can always be decomposed.
        cases h2
        case inl h23 =>
          -- Disjunctions on the left can always be decomposed.
          cases h23
          case inl h24 =>
            -- Disjunctions on the left can always be decomposed.
            cases h24
            case inl h25 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h22
            case inr h26 =>
              -- Disjunctions on the left can always be decomposed.
              cases h26
              case inl h27 =>
                -- Show the left disjunct based on <expert-advice>.
                apply Or.inl
                -- One of the premise coincides with the conclusion.
                exact h22
              case inr h28 =>
                -- False on the left can always be used.
                apply False.elim h28
          case inr h29 =>
            -- False on the left can always be used.
            apply False.elim h29
        case inr h30 =>
          -- Disjunctions on the left can always be decomposed.
          cases h30
          case inl h31 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h22
          case inr h32 =>
            -- Disjunctions on the left can always be decomposed.
            cases h32
            case inl h33 =>
              -- Conjunctions on the left can always be decomposed.
              let h34 := h33.left
              let h35 := h33.right
              -- False on the left can always be used.
              apply False.elim h34
            case inr h36 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h22
      case inr h37 =>
        -- Disjunctions on the left can always be decomposed.
        cases h2
        case inl h38 =>
          -- Disjunctions on the left can always be decomposed.
          cases h38
          case inl h39 =>
            -- Disjunctions on the left can always be decomposed.
            cases h39
            case inl h40 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h41 =>
              -- Disjunctions on the left can always be decomposed.
              cases h41
              case inl h42 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- True on the right can always be proven directly.
                apply True.intro
              case inr h43 =>
                -- False on the left can always be used.
                apply False.elim h43
          case inr h44 =>
            -- False on the left can always be used.
            apply False.elim h44
        case inr h45 =>
          -- Disjunctions on the left can always be decomposed.
          cases h45
          case inl h46 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h47 =>
            -- Disjunctions on the left can always be decomposed.
            cases h47
            case inl h48 =>
              -- Conjunctions on the left can always be decomposed.
              let h49 := h48.left
              let h50 := h48.right
              -- False on the left can always be used.
              apply False.elim h49
            case inr h51 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
  case inr h52 =>
    -- False on the left can always be used.
    apply False.elim h52



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_653636331198393515920956430919 : (((((((p5 ∧ (((((p2 ∨ p1) ∨ p2) ∨ p4) ∨ p4) ∨ p1)) ∧ ((False ∨ True) ∨ (p5 ∧ (p2 ∧ p3)))) ∨ p2) ∧ p1) ∨ (True ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228056022584579287292252248186 : ((p4 ∧ (p1 ∧ p3)) ∨ (p1 ∨ (p3 ∨ (p3 → (True ∧ (((True ∧ (((p1 ∧ p4) ∧ False) → p2)) ∨ (False → (p4 ∨ p1))) ∨ (p5 ∧ p2))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123914114362497147913594548069 : ((((((p2 → p2) → p1) ∨ (((p4 ∧ p2) ∨ p2) ∨ True)) → p2) ∧ (((p4 ∨ (p2 ∨ (p4 → (False ∧ False)))) → True) ∧ p1)) → (True → p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h7 : (((p2 → p2) → p1) ∨ (((p4 ∧ p2) ∨ p2) ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h8 := h3 h7
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50183957277762443400608116716 : ((((((p5 ∨ (p4 ∧ (False → (False ∨ p5)))) ∧ p5) → ((p3 ∨ (p4 → (p1 ∧ True))) ∧ True)) ∧ p2) ∨ (False ∨ ((True ∧ p2) ∨ True))) ∨ p4) := by
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
theorem thm_5_vars_48872622467023221681569144705 : (((True → ((((True ∧ p2) ∨ p2) ∨ (((p3 ∨ p4) ∨ (((p4 ∧ True) → True) ∨ (p1 → p4))) ∨ p4)) ∧ False)) ∧ ((p5 ∧ p4) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350066258088372774181113419202 : (p4 → ((((((p4 ∨ False) ∧ ((True ∨ (p2 → p1)) → ((p5 ∨ p4) → False))) ∧ ((p1 → (p2 → False)) ∨ p1)) → False) ∨ (p1 ∧ True)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h8 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h9 : (True ∨ (p2 → p1)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h10 := h6 h9
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h11 : (p5 ∨ p4) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h12 := h10 h11
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h14 : (True ∨ (p2 → p1)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h15 := h6 h14
      -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
      have h16 : (p5 ∨ p4) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h15, we can now drive its conclusion.
      let h17 := h15 h16
      -- False on the left can always be used.
      apply False.elim h17
  case inr h18 =>
    -- False on the left can always be used.
    apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119436365639179851839382778065 : ((p4 → (((((((p4 ∨ False) ∧ (p3 ∧ False)) ∧ p3) ∨ p4) ∧ (False → p3)) ∧ (p1 ∨ p2)) ∨ ((p4 ∨ (p1 ∧ True)) → False))) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_797628558294801840471998789971 : (((p1 → (((((p2 → p5) ∧ True) ∧ (False → (p3 ∧ p5))) ∧ (p3 ∧ (((p4 ∨ (p1 → False)) ∨ ((p5 ∧ p5) ∧ p2)) → p5))) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324753769830751116286502360279 : (p5 ∨ ((True → (False ∧ True)) → ((((True ∧ p1) → p1) → p4) ∧ ((((p2 ∧ (p2 ∨ p3)) ∨ ((p2 → p4) ∧ (p4 ∧ False))) ∨ p2) ∧ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h6
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- False on the left can always be used.
  apply False.elim h8
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h9 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h9
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303804029297692849126330176974 : (p1 ∨ ((((((True → (p3 ∧ p5)) ∧ True) ∨ p3) ∧ ((((p4 ∨ (True ∧ (p3 → p3))) → (False ∧ (p1 → p3))) → p4) ∧ p4)) → p3) ∨ p2)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h3.left
    let h8 := h3.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h10 := h5 h9
    -- We need to get the left conjuct of h10 based on <expert-advice>.
    let h11 := h10.left
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h3.left
    let h14 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38839667210291897850536699616 : (((((p4 → p4) ∧ p3) ∧ ((p3 ∨ (p2 ∧ p1)) ∧ (((p2 ∨ True) ∨ ((p2 ∨ (True ∨ (p2 ∧ p4))) ∨ True)) → (p2 ∧ p1)))) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175309335198407255359193359545 : ((p4 ∨ ((p2 ∨ (((True ∧ p1) → p5) ∨ (p1 ∨ ((p5 → p3) ∨ p4)))) ∧ True)) → (p3 → (p1 ∨ ((p5 ∨ ((p5 → p3) ∨ p2)) ∨ p4)))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h10
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h12
        case inr h13 =>
          -- Disjunctions on the left can always be decomposed.
          cases h13
          case inl h14 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Implications on the right can always be decomposed.
            intro h15
            -- One of the premise coincides with the conclusion.
            exact h2
          case inr h16 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198293934832568983321517544035 : ((p1 ∧ ((p5 → (p1 → (False ∨ p3))) ∧ p1)) ∨ ((((p5 → ((p1 ∧ p2) ∧ p4)) ∨ p2) ∧ ((p3 → p5) ∨ (p2 ∧ p3))) ∨ (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_775259496605664039429341643237 : (((False ∨ ((False → p4) → (((p3 ∧ p5) ∧ p1) ∨ (p4 ∨ ((p3 → ((False ∨ ((True ∨ False) ∨ False)) ∧ p3)) → ((p2 ∧ p3) → p2)))))) ∨ False) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351868624745969009060533290486 : (p4 → (((((p2 → (p1 ∨ p5)) ∨ (p3 ∧ p2)) ∨ p2) ∨ True) ∧ ((p3 → p3) → (((True ∧ ((p4 ∧ p1) ∧ (False ∨ False))) ∨ p3) → p3)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h11 =>
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325838351177511467175335603366 : (p5 ∨ (p3 ∨ (p1 ∨ (((((p2 ∧ p4) ∧ ((((((p4 ∨ True) ∨ p2) ∨ p5) → True) ∨ p2) → p1)) ∧ (p4 → p1)) ∧ p4) → (p1 ∨ False))))) := by
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
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h10 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h11 := h5 h10
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325624632531440908942853599779 : (p5 ∨ (False ∨ ((p4 ∨ ((((False ∧ (p5 ∧ True)) ∧ (True → ((p2 ∨ (p5 ∧ p2)) → p5))) ∧ ((False ∧ p1) → p2)) ∧ False)) ∨ (True ∨ False)))) := by
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
theorem thm_5_vars_66279853290251775761970674578 : ((p5 ∨ ((p2 → (p5 ∨ p5)) → ((p4 ∧ (((p5 → p1) → (((p4 → p3) ∧ True) ∧ ((p4 ∧ p4) → (p2 → p4)))) ∨ p3)) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255781448090702954888992153315 : ((True ∨ False) → ((((((p1 ∧ ((False → p2) → (p3 ∨ p5))) ∧ p3) ∨ (False → ((False ∨ p2) ∧ ((p1 ∧ p4) ∧ p5)))) ∨ False) ∨ False) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h3
    -- False on the left can always be used.
    apply False.elim h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178345468661414813128578085542 : (((True ∧ ((p5 ∨ p2) ∨ ((p5 ∨ p2) ∧ (p5 → False)))) ∨ (p2 ∨ p1)) ∨ (((False → p3) → p2) ∨ ((True ∧ (p4 ∨ (True → p5))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258359839188744068045641745016 : ((p5 ∨ False) → ((((p4 → p1) ∨ (p2 ∨ ((p1 ∨ p4) → (True → False)))) → (p4 ∨ p1)) ∨ ((p4 ∨ (p2 → p3)) ∨ (p1 → (p1 ∧ p5))))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114036537025084359003153990264 : ((((p3 ∨ ((True → (p5 ∨ ((((p5 → p5) → p4) ∨ False) ∨ p5))) → (p5 ∧ (p1 → p5)))) → p2) ∨ ((p2 ∧ p1) → p2)) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613310512074257806992568450387 : (((((((p1 ∨ p1) ∨ p4) ∨ (((((p1 ∨ p2) → p2) ∨ p2) → p1) ∧ ((p5 → p3) ∧ ((p1 ∧ True) ∨ p2)))) → (p5 ∨ p2)) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_44898841438885579757351102104 : ((((p4 ∧ (p5 ∧ p1)) → ((p1 ∨ ((((p3 → (False → p2)) ∧ (p4 → p4)) ∨ p3) ∧ True)) → (True ∨ ((p5 ∧ p5) ∨ p1)))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_188428316176816976181937177238 : (((((False ∨ p5) ∧ p4) ∨ (p3 ∧ (p4 → p2))) → True) ∧ ((True ∧ ((p4 ∨ ((True ∧ (p2 ∧ (False → p2))) → p5)) ∨ True)) ∨ (p4 → p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307682357064904660832641414948 : (p1 ∨ (p2 → ((p3 ∧ ((True ∧ p1) ∨ ((p5 ∨ ((((False → (p2 ∨ (p1 ∨ p2))) → p1) ∨ False) ∧ p2)) ∧ p4))) ∨ (p3 → (False → p5))))) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_9697319279509748073493989564 : ((((p3 ∨ p2) ∨ (((p1 → (True → p3)) → ((((True ∧ (((True → (p2 ∧ p5)) ∨ p5) ∧ p2)) → p2) → p5) ∧ p4)) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248181702922905800271732622351 : ((p2 ∨ False) ∨ (p3 ∨ (((((p2 → (p2 ∧ False)) ∧ (p1 ∨ p5)) ∨ ((True ∨ (((True ∨ p2) → p2) → p5)) ∨ p2)) ∧ (True ∨ p1)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63330471009966894997527993246 : ((p5 ∧ ((True ∨ p1) → (((((p5 ∧ (p1 ∨ p3)) ∧ True) ∧ True) ∨ ((False ∧ ((True ∨ p1) ∨ p4)) ∨ (p4 ∧ (p3 ∨ p1)))) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352403398967599417264482938716 : (p4 → (((p5 → False) → p3) ∨ ((p2 ∧ ((((p2 → (((p1 → p1) → p4) ∧ p1)) ∧ p5) ∧ p3) ∨ (False ∧ p5))) ∨ ((p1 ∧ False) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39749876893794824353354965991 : (((True → ((((True ∨ ((((p1 ∧ (False ∧ (p3 ∨ p1))) ∨ (((p5 ∨ p2) → p2) ∨ p4)) → p1) → p4)) ∨ p3) ∧ p5) ∨ False)) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52673927840667396804842435069 : (((p1 ∨ ((p2 ∧ (True → ((p3 ∧ (p1 ∧ False)) ∨ (True → False)))) ∨ True)) ∨ (((p2 ∨ (p3 → p2)) → ((p5 ∧ False) → False)) → p2)) ∨ p4) := by
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
theorem thm_5_vars_123964269230663677460926515724 : (((((p2 → (p4 ∧ p1)) ∨ ((p4 → True) ∧ (p2 ∨ True))) ∧ p5) ∨ (((p3 ∨ (p5 ∨ True)) → (p5 ∧ (False ∨ True))) ∧ p1)) → (p4 ∨ True)) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134169569883054623797844919881 : (((((p3 → ((p3 ∨ (p1 → p3)) → ((p2 ∧ (True → p4)) ∨ p5))) → p4) ∨ ((p2 → p5) ∨ (p4 ∧ p1))) ∨ p4) ∨ (True ∨ (p2 ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_868352242189748390834568619216 : (((((True → p2) → ((True → (p2 ∧ p4)) → (((p1 ∨ (False ∨ ((p4 ∨ (p5 ∧ True)) ∧ p4))) ∨ (True → p4)) ∨ (p5 → p5)))) → False) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((True → p2) → ((True → (p2 ∧ p4)) → (((p1 ∨ (False ∨ ((p4 ∨ (p5 ∧ True)) ∧ p4))) ∨ (True → p4)) ∨ (p5 → p5)))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42807026666484616961035263694 : (((p1 → ((False ∧ (p1 → (((p5 ∨ p4) → ((p4 → ((p4 ∧ False) ∧ p2)) → (((p5 → p2) ∧ True) ∨ p2))) → p4))) ∨ p1)) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343207950285018784694094548850 : (p2 → (((p3 ∨ p4) ∨ True) → (True → (((False ∧ ((True ∨ False) → (p5 ∧ p4))) → False) → ((((p3 → (True ∨ False)) ∨ p4) → p3) ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197755448719933068957596531102 : (((p3 ∧ (p1 ∨ p1)) ∧ (p2 ∨ (False ∧ p1))) ∨ (p2 → (((p1 → p3) ∨ (((False ∧ (p3 ∨ p2)) ∨ (p5 → (p5 ∨ p3))) ∨ p1)) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184950561907361582880647535529 : ((((True ∨ p1) ∨ p5) → ((p1 → p4) ∨ ((p2 → p1) → False))) ∨ ((p3 → False) → (((((p1 ∧ p2) → (p2 ∧ p5)) ∧ False) → p2) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157922943050330456370114831097 : (((p3 → (p1 → (p4 → (p4 → (p3 → (p4 ∨ False)))))) → (p2 ∧ (p2 → ((True ∨ p3) → p1)))) ∨ (False ∨ (p1 → ((False ∧ True) → p1)))) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248745391828879861350714119696 : ((p3 ∨ p3) ∨ (((True ∧ (False → p2)) → (p2 → (((p4 → (p5 ∨ (p5 ∧ p1))) → (False ∧ ((p2 → p5) ∨ p5))) ∨ (False ∨ p2)))) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44346454408652984692806503123 : (((((p2 → p5) ∧ ((True ∨ (p2 ∧ (p5 → (p3 → p2)))) ∨ ((True ∧ p4) → True))) → (False ∧ (((p4 ∧ p1) → p2) ∧ p5))) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783701247159125356475087597693 : (((p3 ∨ ((((p4 → True) ∨ (p4 → p2)) ∧ p2) ∨ (((p2 ∧ p2) ∧ ((((p3 → p4) ∧ p2) ∧ ((p3 ∨ False) ∧ p3)) ∧ p1)) ∨ True))) ∨ p3) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250045554708325378752025285754 : ((True → p3) ∨ ((p3 → (False ∨ (p4 → (p1 ∧ p2)))) ∨ (False ∨ (((p1 ∧ (((p5 ∧ (p4 → p5)) → True) ∨ True)) → p1) → (True ∨ p2))))) := by
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
theorem thm_5_vars_737909284658821804121140623978 : ((((True ∧ p3) ∨ (((((((p2 ∧ p3) ∧ ((p4 → p2) ∧ p5)) ∨ (((True → p4) ∨ p1) ∧ True)) ∨ p2) → (p1 ∧ p3)) → p4) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140786350292687463156424251483 : ((((((True → (False → p2)) ∧ False) ∨ (p2 ∧ p2)) → (False ∧ p5)) ∧ ((True ∧ ((p3 → (p5 → p1)) → p2)) ∧ p3)) → ((p2 → p5) ∨ p2)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h8
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h9 : (((True → (False → p2)) ∧ False) ∨ (p2 ∧ p2)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h8
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h10 := h2 h9
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- One of the premise coincides with the conclusion.
  exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231126325942522016729855051955 : (((p1 ∨ p1) ∨ p3) → (p2 → ((((((p5 → p1) → False) → p3) ∨ p5) ∧ (((p1 ∨ (p1 → p5)) ∧ p4) ∧ p5)) ∨ ((p2 ∨ False) → True)))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340167441167002641450026710606 : (p1 → (p4 → ((p5 ∨ ((False ∧ (p4 ∧ p4)) ∧ (((((True → p3) → p5) → p2) → (p2 → p2)) ∨ p4))) ∨ ((p5 ∧ (p3 → p2)) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



