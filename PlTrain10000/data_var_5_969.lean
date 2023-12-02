variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135371954558415994428355975391 : ((((p1 ∨ (p2 → (((p5 ∧ (True → p4)) ∨ ((p2 ∧ False) ∧ (p2 ∧ p4))) → p1))) ∧ p4) ∨ (p4 ∧ (False ∨ p5))) ∨ (False → (True ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37472750284592425713475104750 : (((((((False ∧ False) ∨ True) → (p3 ∨ p5)) ∨ (p3 → ((p4 ∧ False) ∨ (True ∨ (False ∧ (((True ∨ p4) ∨ p1) ∧ p1)))))) ∨ p3) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669456306572382111398290346840 : (((((p5 ∨ (p3 → (((((True ∧ (p3 ∨ (p1 ∨ p3))) ∧ True) → p5) ∨ p4) ∨ (p3 → True)))) ∨ (p4 ∧ p5)) ∨ (False → (p4 ∨ p2))) ∨ False) ∧ True) := by
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
theorem thm_5_vars_234882388257780116135226788097 : ((p5 → (p4 → p3)) → (True ∧ ((((p2 → ((True ∨ (p1 ∧ p4)) ∧ True)) → p5) ∨ True) ∧ ((p4 → (p1 ∨ (False → (p1 ∨ p2)))) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_629290414283929141635385714584 : ((((((((p1 → (((p5 → p1) → (True ∨ ((False ∨ True) → (p4 ∨ p4)))) ∨ (p2 ∨ False))) ∧ True) ∨ (p2 → True)) → True) ∨ p3) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348996731742077168078440425380 : (p3 → (p4 ∨ ((((False ∨ p2) → p5) → (p1 ∨ False)) ∨ ((p4 ∧ (p2 ∧ (p4 ∨ p2))) → ((((True ∨ (p2 ∨ False)) ∧ True) ∧ p1) → p2))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h2.left
    let h10 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h14 =>
      -- One of the premise coincides with the conclusion.
      exact h14
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h2.left
      let h18 := h2.right
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h21 =>
        -- One of the premise coincides with the conclusion.
        exact h19
      case inr h22 =>
        -- One of the premise coincides with the conclusion.
        exact h22
    case inr h23 =>
      -- False on the left can always be used.
      apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190854257983031020914128716522 : ((((p5 ∧ ((p2 ∨ False) ∨ p1)) ∨ p4) → (p3 ∨ False)) ∨ (p3 ∨ (((p5 ∨ (((True → False) ∨ ((p5 → False) ∨ p5)) → p1)) ∨ p3) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115386894578675680125759332711 : ((((True → False) ∧ ((p3 → p1) → (p5 ∨ p3))) ∧ (((p2 ∧ (False ∧ (p5 ∨ p2))) ∨ (p2 → ((p1 ∨ p5) ∨ p4))) → p3)) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54359655646216527721268872578 : (((p4 ∨ (((p2 ∨ p1) ∨ (False ∨ False)) → p1)) ∧ (((True → ((p2 → ((p1 ∧ p5) ∨ p3)) ∨ True)) ∨ (p4 ∧ (False → p5))) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159561369385984280752116922941 : (((p2 ∨ ((((p3 ∨ (p3 ∨ (p5 ∨ ((p2 ∧ (True ∧ p5)) → False)))) → p5) ∨ True) → p2)) ∧ p3) → (((p3 ∧ (p5 ∨ False)) ∧ p2) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
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
theorem thm_5_vars_139328589914106321253870880745 : (((p2 ∨ ((p4 → (((((p3 ∧ p4) → False) ∧ True) ∨ False) → ((((p2 ∧ False) → p1) → False) ∧ p5))) → False)) ∨ True) → ((p3 ∨ p2) ∨ True)) := by
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
theorem thm_5_vars_809761816742137649731641890765 : (((p5 → ((((p3 ∧ p5) → (p3 ∧ (((True ∨ False) → ((p2 ∨ False) ∨ (p3 ∧ (True ∧ p4)))) ∨ (p1 ∧ p1)))) → p2) ∨ (True ∨ p1))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115578759421488312074323851713 : ((((p2 ∨ (p1 → False)) ∧ (p1 ∨ p1)) ∧ ((p3 ∧ p1) ∨ (p3 ∨ (((p4 ∨ False) ∨ p1) ∧ (p2 ∧ ((p1 ∧ True) ∧ p5)))))) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617706545528719737297647207586 : ((((((p4 ∧ p3) ∧ (p2 ∧ (True → p4))) ∨ (((p3 ∨ (((True → p4) ∧ ((p4 ∨ False) ∧ (p1 ∧ p1))) ∨ p4)) ∧ p4) ∨ p2)) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_337120115732033312358275858901 : (p1 → ((True ∧ (False ∨ ((p3 ∨ ((((True ∨ p1) ∧ (True → True)) → (p1 ∧ p3)) ∧ (p2 ∨ ((p2 → p1) → False)))) ∧ False))) ∨ (False → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111973627016936311056801742247 : (((((p3 ∨ ((p1 ∧ False) ∧ p2)) ∧ p5) ∨ (((p1 ∧ (False → p4)) ∧ p2) → (False → ((p4 ∧ (p5 ∨ p2)) ∨ p4)))) ∨ p4) ∨ (p1 ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41347133954319552372667787985 : ((((True ∧ (((p3 → ((p2 ∨ (p2 → False)) ∧ p3)) ∧ (p1 ∧ (p4 ∧ True))) → p3)) ∨ (((p1 ∨ (p5 → p5)) → p4) ∧ p4)) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191203849392049603574870744099 : ((((False ∧ p5) → p2) → (p5 → ((False ∨ p4) ∧ p4))) ∨ (((p3 ∧ ((p5 → ((False ∧ (p3 ∧ (p4 ∨ True))) ∨ True)) ∧ p1)) → True) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137913062441491204863224935633 : ((p4 ∨ (((True ∧ p5) → (p5 → p2)) → ((p2 ∧ ((((p5 → False) ∧ ((p1 → p1) ∧ p3)) ∧ p4) ∧ p1)) ∨ p2))) ∨ ((p3 ∧ False) → p3)) := by
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
theorem thm_5_vars_134117450223722647185457198600 : ((((((p1 → (p5 ∨ (p4 ∨ ((False → ((p5 → (True ∧ True)) ∨ p4)) → p2)))) ∧ p3) ∨ p1) ∨ (p5 → p5)) ∨ p4) ∨ ((True → p1) ∨ p4)) := by
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
theorem thm_5_vars_608657820083087865939407140330 : (((((((True ∨ (p2 ∨ ((True ∨ True) ∧ ((p3 → False) ∧ (p4 → True))))) → ((False ∧ (p4 → False)) ∨ False)) ∨ (p4 ∨ p5)) ∨ True) ∨ p5) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_725161623731023300228160058774 : ((((p1 → (p2 → False)) ∧ ((p1 ∧ (((p4 → p2) → ((True ∨ p4) → p1)) ∧ (False → ((p3 ∨ (False ∧ p5)) → (p2 ∧ False))))) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_627442868859216343092783148924 : ((((((p2 ∧ ((p5 → ((p5 ∨ p1) ∧ ((p5 → p1) ∨ (p3 → (True → (p5 → False)))))) ∧ ((p4 ∧ p4) → p4))) → False) ∧ p4) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_586750610449929144311142528674 : (((((p1 ∧ (p5 → ((((p5 ∨ (p4 ∧ False)) → False) → p3) → ((p5 ∧ p1) ∧ ((p2 ∨ ((p5 → p4) ∨ p2)) → True))))) ∧ p2) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61336281083076695243303818881 : ((p1 ∧ ((((p5 ∨ p3) ∧ (((((p3 ∧ False) ∨ ((p1 ∨ True) ∧ p2)) ∧ (p3 ∨ (p2 ∧ True))) → (True ∧ True)) → True)) ∨ p3) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306214104890316329835179316446 : (p1 ∨ (((True → p3) ∧ p4) → (p4 → (p1 ∨ (p5 ∨ (p2 ∨ (p5 ∨ ((p5 ∨ (p2 ∧ (p2 → p1))) → (False → (p2 → (False ∧ p5))))))))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h6
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257605115757433305910608126854 : ((p3 ∨ p2) → ((((p5 ∨ p4) ∨ ((p1 → True) ∧ (p4 ∨ (p3 ∨ (True ∧ (p2 ∧ (p2 ∨ p4))))))) ∨ (p3 ∨ ((p5 ∨ p5) → p2))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h6 =>
      -- One of the premise coincides with the conclusion.
      exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_625735824412626115169892644174 : ((((p1 → ((p3 → (p1 ∧ p2)) ∧ (((p1 ∨ (p5 ∧ (((p4 ∨ (((False → p1) ∨ False) → p5)) ∨ True) ∧ p1))) → p3) ∨ p1))) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_346644781261394566472651820794 : (p3 → ((p2 → (((p1 ∧ (p1 ∧ (p1 ∧ (((p4 ∨ p4) ∧ False) ∨ ((p5 ∨ p4) ∨ False))))) ∧ (p4 → True)) ∧ p3)) ∨ (True ∨ (p3 ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325856129399160180598045446423 : (p5 ∨ (p4 ∨ (((p3 ∨ (p1 ∧ (False ∨ (p4 ∧ ((p4 ∨ p2) ∨ True))))) ∧ (True ∨ (p3 ∨ ((True ∨ ((p4 ∧ p3) → True)) ∨ p1)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_688393687806859721587661488112 : ((((p1 ∧ (((p5 ∧ True) ∧ ((False → p4) → (False ∨ p4))) ∧ ((p5 ∧ p5) ∧ p5))) ∧ (((p2 ∨ p1) ∨ (p2 ∨ (True ∧ False))) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137305469624348113769526733630 : ((p2 ∧ (((((p2 ∨ (p5 ∧ p3)) ∨ (((p2 → p3) ∧ p2) ∨ (p1 → False))) → True) ∨ p5) → (False ∧ (p3 ∧ p3)))) ∨ ((False → p4) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205195678558914490804459566015 : (((False → (p4 ∧ p4)) ∧ (p3 ∧ p3)) ∨ ((((p5 ∧ False) ∨ p4) ∧ (p2 ∨ (((True → ((p4 → p4) ∧ p2)) → p5) → p3))) ∨ (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_633841383525039854602801454630 : (((((((p1 → (p5 ∨ (p1 ∨ False))) → (p5 ∨ (((p2 ∧ True) → (True ∧ False)) ∨ (p4 ∨ (False ∨ p2))))) ∧ p5) → (p2 ∧ p1)) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198609733776338519011406025782 : ((p2 ∨ ((False ∨ p5) ∨ (p3 ∧ (p1 → False)))) ∨ (True ∨ (((p5 ∧ ((p5 ∨ p1) ∧ ((True → p5) ∨ (False → p5)))) ∧ p3) → (True → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172282303905969563614123582783 : (((p5 ∧ ((p1 ∧ p5) ∧ (False → (p3 → p5)))) ∨ (p1 → (False ∨ (p2 → p3)))) ∨ (False → ((((p4 ∧ (p2 → True)) ∧ p5) ∧ p1) ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126178226392314679063892596369 : ((True ∧ (True → ((((True ∧ (True ∧ p2)) ∨ (True ∨ (p5 ∨ p4))) → ((True ∧ p4) ∨ (False ∧ p5))) ∧ (p2 ∧ (p1 → p4))))) → (p2 ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137914601011548371888155739804 : ((p4 ∨ (((p4 → False) ∧ p1) ∨ ((((p5 ∧ (False ∨ p3)) ∨ p4) ∧ (p4 ∨ (p2 ∧ True))) ∨ (p4 → (p5 ∨ p2))))) ∨ (p1 → (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774503957164787981809945037197 : (((False ∨ ((p1 ∧ (p4 ∧ (((p1 ∧ (((p3 → True) ∧ False) → p2)) ∨ False) ∨ False))) ∧ (((True ∧ (p3 → p5)) ∧ True) ∨ (True ∧ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208339231227861950974118734447 : (((p3 → p4) ∧ ((p2 ∧ True) → p4)) → (((p1 → ((p1 → ((p2 → True) ∧ p3)) ∨ ((False → (p3 ∧ p3)) ∨ p4))) ∧ True) ∨ (p1 ∧ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h5
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345691231934968076500447452800 : (p3 → ((p4 ∨ (True → (((p3 → p2) → p3) → (((p1 ∨ p2) → ((p5 → (p2 ∨ (p5 ∨ p2))) → (p5 ∨ True))) → (p2 ∨ p1))))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_169371521129129108686902187804 : (((((p4 ∨ (p3 ∨ p1)) ∧ ((p4 ∨ (p3 → (p5 → p3))) ∧ p1)) ∧ p3) ∨ True) ∧ (False ∨ (((p5 → (p5 ∧ (p1 → p1))) ∧ p5) → p5))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_647494668714018974959475048810 : ((((p4 → (p4 → ((True → (((p3 ∧ False) ∨ (p1 → (p3 → True))) → True)) ∧ ((p3 ∧ (p5 ∧ True)) → ((p2 ∧ p1) → p2))))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138139923958368923871837304503 : ((p1 → ((((p3 ∨ p5) → ((p2 ∨ p5) ∨ (((False → (p3 ∨ p4)) → (p3 ∨ True)) ∨ (p1 ∧ p2)))) ∨ True) ∧ p5)) ∨ ((p1 → p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171762130461106817460266409315 : (((((p1 → ((True ∧ p4) ∨ ((False → p3) → p2))) ∨ (p5 ∨ p4)) → p2) → p1) ∨ (p4 ∨ (((False → (p4 ∨ False)) → (False → False)) ∨ False))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_443845948549658045288566059195 : (((((p3 ∨ (p3 ∧ p2)) ∨ ((False ∧ p3) ∨ ((p2 → False) → (((p5 → (p2 → (p3 → p1))) → p4) → p4)))) ∨ ((True → True) → True)) ∧ True) ∧ True) := by
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
theorem thm_5_vars_691034846502086673379604989751 : (((((p4 → (False → ((False → (True → (False → False))) ∧ p1))) ∧ ((p4 → p3) → False)) → (p1 ∧ ((((p2 → p4) ∨ True) ∧ p3) ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126692657210047389109813894895 : ((p4 ∧ ((p3 ∨ (((((p4 ∨ p5) ∧ p1) ∨ (False → (p1 → p5))) ∧ p1) → ((p1 → p4) → (True → (p3 ∨ True))))) → p1)) → (p1 ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p3 ∨ (((((p4 ∨ p5) ∧ p1) ∨ (False → (p1 → p5))) ∧ p1) → ((p1 → p4) → (True → (p3 ∨ True))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h5.left
    let h9 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h16 := h3 h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_203837469622677297848769336141 : ((False → ((p3 ∧ (p1 ∨ p2)) → p4)) ∧ (p3 ∨ (((p2 ∨ p5) → (((p2 ∨ (p4 ∨ p5)) → (p4 ∧ (p1 ∧ p3))) ∨ False)) ∨ (False ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h1
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116052966209623490192649056413 : (((p4 → ((True ∧ p3) ∧ True)) → (False ∨ (p2 ∧ (((p5 ∧ (True ∧ (((p1 → p5) ∨ p1) → False))) ∧ p3) ∧ (p3 ∧ p5))))) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_893349809061459838804944120123 : (((((((p3 → p5) → (p2 → (p2 ∨ p2))) → True) → (((p5 ∧ p1) ∧ False) ∧ (p4 ∨ (p3 → (p5 → False))))) ∧ (p5 ∧ (True ∨ p2))) → False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : (((p3 → p5) → (p2 → (p2 ∨ p2))) → True) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h9 := h2 h7
    -- We need to get the left conjuct of h9 based on <expert-advice>.
    let h10 := h9.left
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h13 : (((p3 → p5) → (p2 → (p2 ∨ p2))) → True) := by
      -- Implications on the right can always be decomposed.
      intro h14
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h15 := h2 h13
    -- We need to get the left conjuct of h15 based on <expert-advice>.
    let h16 := h15.left
    -- We need to get the right conjuct of h16 based on <expert-advice>.
    let h17 := h16.right
    -- False on the left can always be used.
    apply False.elim h17
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_706915083927426540915793063586 : ((((((p1 ∨ (p5 ∨ (p2 ∧ p4))) ∨ p3) ∨ False) ∨ (((False ∧ p5) ∧ (p1 ∧ (p2 → (True ∨ ((False ∧ False) ∨ p1))))) → (p5 → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337109562469700380731974326313 : (p1 → (((True ∧ p3) ∧ (((((p3 ∨ p2) ∧ p5) → (p4 ∧ (p1 ∨ True))) → (p3 ∧ (p3 → (True ∨ p4)))) ∨ (p2 ∨ p3))) ∨ (p5 → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337137392350925948290181066373 : (p1 → ((p3 ∨ (p5 ∧ ((p2 ∧ (p4 ∨ ((p5 ∨ (p4 ∨ p4)) ∧ ((p5 ∨ (False → (p3 → p5))) ∧ (p3 → True))))) ∧ p1))) ∨ (p3 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64894021719971232890158247862 : ((p2 ∨ ((p5 ∨ (((p3 ∨ ((((p2 ∨ p4) ∧ ((p4 ∨ p2) ∧ p3)) ∨ p3) → p4)) ∧ p3) ∧ (p3 ∧ p5))) ∨ ((p3 ∧ p2) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148635397471283056180717485850 : (((p3 → (((p1 → p1) ∨ ((True ∨ True) → p5)) ∨ True)) → (((p4 ∨ p4) → (p2 ∧ p4)) ∨ (p2 ∨ p5))) ∨ ((p2 → p2) ∨ (p4 ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111868012151513262234250454168 : ((((((p1 ∨ p2) ∧ (((p2 ∧ (True → p2)) ∧ p2) ∨ ((p2 ∨ p5) → p4))) → p3) ∨ (False ∧ ((p2 ∨ p3) → p4))) ∨ True) ∨ (p3 → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37518644998959999700782939080 : (((((p2 → p2) → (p3 ∨ (((((p5 ∧ (p1 → (False ∧ ((True → p1) → p4)))) → p1) ∧ (p4 → p3)) ∨ p3) ∨ p2))) ∨ p3) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51311148526515191571418634748 : (((p3 ∨ ((p1 ∧ ((p4 ∧ (True → False)) → ((p4 ∧ (p2 → False)) ∨ p5))) ∧ (True ∨ p3))) ∨ ((True ∧ (p4 ∨ (p2 → p3))) ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178060726960739537456671522821 : ((((((p1 ∨ (p4 ∧ p4)) ∨ ((p4 ∨ p2) ∧ p3)) → p4) ∨ True) → False) ∨ ((p3 ∨ True) ∨ (True → (((False ∧ (False ∨ p5)) ∨ p4) ∧ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112802404349068853727606332085 : (((((True ∨ (p2 → p4)) ∧ (p3 → p5)) ∨ (((True ∨ p5) ∧ ((p5 → True) ∧ (p5 ∧ (p1 → p2)))) → (False ∧ True))) → p4) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114087969132743251383593513794 : ((((p4 ∧ p2) ∨ ((((p2 → True) → (((False ∧ p3) ∧ (True ∨ (False ∨ p1))) ∨ p4)) ∨ p1) → False)) ∨ ((p5 ∧ False) → p5)) ∨ (True ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_340554567296909081144141707027 : (p2 → (((p3 ∨ p4) ∨ ((((p3 ∨ (p5 ∧ ((((p3 → (p4 → False)) ∨ p2) ∨ (False → p1)) ∧ (True ∨ False)))) → p3) ∨ p2) ∨ True)) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_174564448149796039614790692544 : ((((p4 ∨ True) ∨ (False ∨ p4)) ∧ ((((True ∧ False) → p1) ∨ (p3 → True)) → False)) → (((p2 → ((p4 ∨ False) ∧ p4)) ∨ (p5 ∨ p4)) → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h1.left
    let h5 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h8 : (((True ∧ False) → p1) ∨ (p3 → True)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h9
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h10 := h5 h8
        -- False on the left can always be used.
        apply False.elim h10
      case inr h11 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h12 : (((True ∧ False) → p1) ∨ (p3 → True)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h13
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h14 := h5 h12
        -- False on the left can always be used.
        apply False.elim h14
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- False on the left can always be used.
        apply False.elim h16
      case inr h17 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h18 : (((True ∧ False) → p1) ∨ (p3 → True)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h19
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h20 := h5 h18
        -- False on the left can always be used.
        apply False.elim h20
  case inr h21 =>
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h1.left
      let h24 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h25 =>
        -- Disjunctions on the left can always be decomposed.
        cases h25
        case inl h26 =>
          -- One of the premise coincides with the conclusion.
          exact h22
        case inr h27 =>
          -- One of the premise coincides with the conclusion.
          exact h22
      case inr h28 =>
        -- Disjunctions on the left can always be decomposed.
        cases h28
        case inl h29 =>
          -- False on the left can always be used.
          apply False.elim h29
        case inr h30 =>
          -- One of the premise coincides with the conclusion.
          exact h22
    case inr h31 =>
      -- Conjunctions on the left can always be decomposed.
      let h32 := h1.left
      let h33 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h32
      case inl h34 =>
        -- Disjunctions on the left can always be decomposed.
        cases h34
        case inl h35 =>
          -- We want to use the implication h33 based on <expert-advice>. So we show its premise.
          have h36 : (((True ∧ False) → p1) ∨ (p3 → True)) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h37
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h33, we can now drive its conclusion.
          let h38 := h33 h36
          -- False on the left can always be used.
          apply False.elim h38
        case inr h39 =>
          -- We want to use the implication h33 based on <expert-advice>. So we show its premise.
          have h40 : (((True ∧ False) → p1) ∨ (p3 → True)) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h41
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h33, we can now drive its conclusion.
          let h42 := h33 h40
          -- False on the left can always be used.
          apply False.elim h42
      case inr h43 =>
        -- Disjunctions on the left can always be decomposed.
        cases h43
        case inl h44 =>
          -- False on the left can always be used.
          apply False.elim h44
        case inr h45 =>
          -- We want to use the implication h33 based on <expert-advice>. So we show its premise.
          have h46 : (((True ∧ False) → p1) ∨ (p3 → True)) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h47
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h33, we can now drive its conclusion.
          let h48 := h33 h46
          -- False on the left can always be used.
          apply False.elim h48



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_672324632255489177691273582392 : (((((((p4 ∧ ((p1 → False) ∧ ((p1 ∧ p2) ∧ (p3 → False)))) → ((p2 ∧ p4) ∧ True)) ∨ (p1 → True)) → p2) → ((p4 ∨ p1) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50277248504574799478579568844 : (((((p4 → p1) ∨ (True ∧ (((p2 ∨ p2) → p5) ∨ (p4 ∧ (True → (True → True)))))) ∨ (p3 ∨ False)) ∨ ((p3 ∧ (p2 → p5)) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638699356135692556150590783667 : ((((((p2 ∧ (p2 ∨ False)) ∨ (p2 ∨ p5)) → (((((((False ∨ p3) ∨ False) → (p3 ∨ False)) → True) ∧ (p3 ∨ p1)) → True) ∨ p3)) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615783743017977679125114031961 : (((((((p2 → (True ∨ (p2 ∧ ((p3 → p4) ∧ True)))) → (p3 ∧ p5)) ∧ p1) ∨ (False → (((True ∨ (p5 ∨ p3)) ∧ p1) → p2))) ∨ p2) ∨ p5) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h1
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h1
    case inr h8 =>
      -- False on the left can always be used.
      apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711735183775289079046477393928 : ((((((p2 ∨ (p1 → p4)) ∧ p2) ∧ p2) ∨ ((((p3 ∨ p1) → (p5 ∨ (True ∨ p3))) ∧ p4) → ((p4 ∧ (False ∨ (False ∧ True))) ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_759118010604323461120529920287 : (((p2 ∧ ((((((p3 ∨ p5) ∧ False) → p5) ∨ False) ∧ (((p3 → (p1 ∧ True)) ∨ (p5 → False)) → ((p3 → False) ∨ p2))) ∧ (p4 ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52010156367945398773899146426 : (((p3 ∧ ((p4 → False) ∨ ((p1 ∧ (p4 ∧ (p3 ∨ (p1 ∨ (p3 ∧ False))))) ∨ p3))) ∨ (True → (p5 ∨ ((p5 ∨ False) ∧ (p5 ∧ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135532946980768349807303572925 : ((((((False ∧ (p3 ∨ (p5 ∧ p2))) → (False ∨ (False → p3))) ∧ p3) ∨ (True ∧ p5)) ∧ (p1 ∨ ((p4 → p3) → False))) ∨ ((p4 ∧ False) → False)) := by
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
theorem thm_5_vars_355630378047855880754724544079 : (p5 → ((p4 ∨ ((p1 ∨ (((p1 → (p2 ∨ (False ∨ (((p3 → (p2 → p3)) ∨ p1) ∨ p3)))) → p2) → p1)) ∧ (False ∨ p2))) ∨ (True ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215533521661593162558294612135 : ((p4 ∧ (p4 ∨ (p2 ∧ p2))) ∨ (((((p4 ∧ p2) → p3) → p1) ∨ (p5 ∧ ((((p4 → (True ∧ p5)) → p1) ∧ p2) → (p2 ∨ False)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_740676649814831528632043217294 : ((((p2 ∨ p3) ∨ ((p2 ∧ ((p5 ∨ ((p5 ∨ (p4 ∧ (True → ((p3 → p2) ∧ p3)))) ∨ (p4 → p4))) ∨ (False ∧ False))) ∨ (True → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37139978626031157566468770243 : (((((((p5 ∧ (p5 ∧ (p5 ∨ ((True → p4) ∨ False)))) → ((p5 → p4) ∧ (False → p2))) ∨ (p5 ∧ False)) → (p4 → p3)) ∧ p3) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214286972280096372108198891907 : (((p4 ∧ (p5 ∨ p1)) → False) ∨ ((p5 ∨ (p1 → p3)) ∨ ((True → p4) → (((p4 ∨ False) ∨ (((p1 → p2) → p2) ∨ p3)) ∨ (p5 ∧ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310124561690737725441667979746 : (p2 ∨ ((((p4 → False) → (p3 ∨ (True ∨ p2))) → (((p3 ∧ p1) ∨ p3) ∧ p1)) ∨ ((p5 → (p1 ∨ True)) → (((p5 → True) ∨ p5) ∨ False)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200306459672603958742427801372 : (((p2 ∧ p5) ∧ ((p4 ∨ (p1 → True)) ∨ p1)) → ((False ∧ ((((False → p5) → p2) ∨ p1) ∧ (p2 → (p5 → (p4 ∨ False))))) ∨ (p5 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119051463791051357533098413162 : ((p1 → (((p2 ∨ p3) → ((p2 ∧ ((((True ∨ p2) ∨ (True ∧ p4)) → p3) ∨ ((p5 ∨ p3) ∧ (p2 ∨ False)))) ∨ p3)) ∨ p3)) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231414200286651725536445387957 : (((p1 → p3) ∨ p5) → (((p5 ∨ (((((p3 ∧ p2) → (p4 ∨ (False → p1))) ∧ (p5 ∧ p5)) ∧ p5) → p4)) ∨ (p2 → p2)) ∨ (p2 ∨ p2))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54701158790576626811666802027 : ((((p2 ∨ ((p2 ∨ p3) ∨ False)) ∧ (p2 → p5)) → (p5 → ((((p2 → p2) → p4) ∨ ((p2 → p1) ∧ p1)) → (p4 ∨ (p1 ∨ p1))))) ∨ p2) := by
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
    cases h5
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h8 : (p2 → p2) := by
        -- Implications on the right can always be decomposed.
        intro h9
        -- One of the premise coincides with the conclusion.
        exact h9
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h10 := h4 h8
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h14 : (p2 → p2) := by
            -- Implications on the right can always be decomposed.
            intro h15
            -- One of the premise coincides with the conclusion.
            exact h15
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h16 := h4 h14
          -- One of the premise coincides with the conclusion.
          exact h16
        case inr h17 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h18 : (p2 → p2) := by
            -- Implications on the right can always be decomposed.
            intro h19
            -- One of the premise coincides with the conclusion.
            exact h19
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h20 := h4 h18
          -- One of the premise coincides with the conclusion.
          exact h20
      case inr h21 =>
        -- False on the left can always be used.
        apply False.elim h21
  case inr h22 =>
    -- Conjunctions on the left can always be decomposed.
    let h23 := h22.left
    let h24 := h22.right
    -- Conjunctions on the left can always be decomposed.
    let h25 := h1.left
    let h26 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h25
    case inl h27 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h24
    case inr h28 =>
      -- Disjunctions on the left can always be decomposed.
      cases h28
      case inl h29 =>
        -- Disjunctions on the left can always be decomposed.
        cases h29
        case inl h30 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h24
        case inr h31 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h24
      case inr h32 =>
        -- False on the left can always be used.
        apply False.elim h32



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136315933487858360898689457956 : ((((p3 → (p4 → p2)) ∨ p5) ∧ ((p3 ∧ (p1 → (((p1 ∨ (p5 ∨ (False → True))) ∧ p1) → (p4 ∧ True)))) ∧ p3)) ∨ ((True ∨ p4) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690670544648065083521460946667 : (((((p2 ∧ (((False ∧ p4) ∨ ((p2 ∨ (p3 ∨ (p2 ∧ True))) ∨ p5)) ∨ True)) ∨ p5) → ((p4 ∨ (False ∨ (p4 ∨ (p1 ∧ p5)))) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191484640387287265948824796760 : ((True ∧ ((p1 ∨ p1) ∧ ((p2 ∧ (False ∨ False)) → p5))) ∨ ((p4 ∨ (p1 ∨ (p5 → ((p4 → False) ∨ (p2 → (True ∨ (p3 ∨ p2))))))) ∨ p4)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165924817501779226032148395671 : (((p2 ∧ p3) ∧ ((False → (False ∨ p5)) → ((((p2 ∨ p3) → (True → p1)) → p2) ∨ p5))) ∨ (((p4 ∧ ((False ∧ p1) → p3)) ∧ False) → p1)) := by
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
theorem thm_5_vars_609860999846785822109521804481 : (((((p1 → ((p1 → False) ∧ (((False ∧ p4) ∨ ((((p5 ∨ True) ∧ False) ∨ (p1 ∨ (p5 → p3))) ∨ (p2 ∨ True))) ∨ p1))) ∨ p5) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_131574953233581772343976496165 : (((p3 → (p3 ∨ p2)) ∧ (((p3 ∧ (p5 → (p4 ∨ (p1 ∧ p4)))) ∨ p1) ∨ ((p2 → (p3 ∨ True)) ∨ (False ∧ True)))) ∧ ((p2 ∧ p5) → p5)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698429086781120205846698757464 : (((((((p3 → False) → p4) → (p2 ∨ False)) ∧ (p5 → (p4 → p3))) ∨ (p3 ∧ ((p4 ∧ ((p3 → (p3 ∨ (p2 ∧ False))) ∨ True)) → True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1458090265956072357688948738 : (((((p5 ∧ ((True → (p2 ∨ (p5 ∨ p1))) → ((p5 ∧ (True → (p5 → False))) ∧ p1))) ∧ True) ∧ (False ∨ p4)) ∧ p5) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48986171725576543165540745770 : (((((p4 ∨ (p1 ∨ p3)) ∨ (((((p1 ∨ (p2 ∨ (p2 → True))) ∨ True) ∨ (p5 ∧ True)) ∨ p1) → p2)) ∨ p1) ∨ ((True ∨ p3) ∨ True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_706760229684313651165651840081 : ((((((p3 ∨ (False → (p3 → False))) → False) ∧ p1) ∨ ((p4 ∧ (True ∨ ((False ∨ False) ∧ (p2 → ((p5 → p5) → (False ∨ True)))))) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809976901671454379088789768338 : (((p5 → ((p1 ∨ ((True → ((p5 ∨ False) → (p3 ∧ ((p4 ∨ p5) ∧ p3)))) ∨ ((p1 ∧ (p2 ∨ p2)) ∧ p3))) ∨ ((p4 ∨ False) ∨ p5))) ∨ p2) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197770997439550087033304178521 : (((p5 ∨ (p2 ∧ p4)) ∧ (p3 → (p4 ∧ p5))) ∨ ((((False ∧ False) → ((p1 ∨ False) → False)) ∨ (True ∨ (((p3 → False) ∧ p4) ∨ p4))) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57741241708225743280758853826 : ((((p5 ∨ p2) → p3) → (((p2 ∧ p3) ∨ ((((p4 → False) ∧ ((p2 → False) → p1)) ∧ (((p4 ∨ p4) → p3) ∧ p5)) ∧ p3)) ∨ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137759100802358164910353304249 : ((p2 ∨ ((True ∧ ((p3 ∨ ((p3 ∨ p2) → (p3 ∨ p1))) ∧ ((True ∨ (True → p1)) ∨ (p2 ∧ (p5 → p4))))) → p2)) ∨ ((p1 → True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_80907159962768847082355482813 : (((((((True ∨ (((False ∧ p2) → (p2 ∧ (p1 ∧ p1))) → p2)) → (p1 ∨ p4)) → (p4 ∨ p4)) ∨ p3) → False) ∧ ((p3 ∧ p3) ∨ p3)) → p2) := by
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : ((((True ∨ (((False ∧ p2) → (p2 ∧ (p1 ∧ p1))) → p2)) → (p1 ∨ p4)) → (p4 ∨ p4)) ∨ p3) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h7
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h10 : ((((True ∨ (((False ∧ p2) → (p2 ∧ (p1 ∧ p1))) → p2)) → (p1 ∨ p4)) → (p4 ∨ p4)) ∨ p3) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h11 := h2 h10
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_127757748304764979489695183075 : ((True → (((((((p2 → (p1 → p5)) → p5) → (p4 ∧ ((p3 → True) ∧ p5))) → p3) → p1) ∧ (p4 ∧ p4)) ∧ (p1 ∧ p5))) → (True ∧ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315130353729216734592531549309 : (p3 ∨ ((False ∧ ((p2 → False) → (p4 ∨ False))) ∨ ((True ∧ ((((p5 ∧ p1) → p4) ∧ False) ∨ (False → (True ∧ (p2 ∨ False))))) ∨ (p4 ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178685433431264228756105628274 : ((((p4 ∨ (p2 ∨ p1)) ∧ p1) ∨ ((p1 → (p1 ∧ (False ∨ p1))) ∨ p5)) ∨ ((True ∧ (p2 → p3)) → (p3 ∨ ((p3 ∧ (p2 → p3)) → p2)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



