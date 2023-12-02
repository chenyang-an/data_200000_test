variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218301054588629097485033533618 : (((p4 ∨ p4) ∨ (p4 → False)) → (((p3 → True) → p4) → (p3 → (((((p3 → True) → (p1 ∧ (p1 ∨ False))) → p4) ∨ (p5 ∧ False)) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h7 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h8 : (p3 → True) := by
      -- Implications on the right can always be decomposed.
      intro h9
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h10 := h2 h8
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249928276455046882470711036621 : ((True → p1) ∨ ((p4 → (False ∧ p5)) ∨ ((p4 → (((p1 ∨ ((True ∨ p3) ∨ p3)) → (p3 → (True ∧ p3))) → p5)) ∨ ((True → p5) ∨ True)))) := by
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
theorem thm_5_vars_260718305660034258103159365204 : ((p3 → p4) → ((p1 → ((False ∧ p2) ∨ (((p5 → ((True ∧ p3) ∨ (False ∧ p5))) ∨ ((True ∨ (p1 ∨ True)) → False)) ∨ p1))) ∧ (True ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656066449340141729054939910059 : ((((((True ∨ (p4 ∨ p4)) → ((p1 → (((False → p1) → p1) ∨ p4)) → (True ∧ True))) → (p1 ∧ (p1 → (True → p1)))) ∨ (p3 ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_664703344379131103146931741274 : ((((False → (((p2 ∨ ((p1 ∧ ((p4 ∨ False) → True)) → ((False → p2) ∨ True))) → p2) ∧ ((False ∧ p1) ∨ (p5 ∧ p3)))) → (p5 ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312003759245117153013340533898 : (p2 ∨ (p4 ∨ (((((p3 ∧ (p5 ∨ ((p3 → p5) ∨ p5))) ∧ p1) ∨ p5) ∨ ((p5 ∧ p5) ∨ (p3 → True))) ∨ ((False → p1) ∧ (False → p2))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194073856606692383989444253323 : ((True → ((((p2 → p1) ∨ False) ∧ True) ∧ (p2 ∧ p3))) → (True ∧ ((((True → ((True ∧ (True ∧ p1)) ∨ True)) ∨ (p1 → p2)) → p4) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658061892918963390901374079686 : ((((p3 ∧ (((p3 ∨ p3) ∨ (((((p4 ∧ True) → (p2 ∨ p4)) ∨ ((True → p1) ∧ False)) ∨ False) → p5)) ∨ (p2 ∧ p3))) ∨ (p1 → True)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135673250932291737983876653274 : (((False → ((p1 ∨ (p2 ∧ ((p1 ∧ p4) → ((p5 ∨ (p5 ∧ False)) → p4)))) ∨ p3)) → (p5 → ((p3 → p5) → p3))) ∨ ((False ∨ p3) → p3)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233321379161096635409296770348 : ((True ∨ (False → True)) → ((p5 ∨ (((p1 ∧ p4) ∧ p4) → (True ∧ ((p3 ∧ p2) ∧ p2)))) → (True → (p4 → ((p3 ∧ (True ∧ p4)) ∨ True))))) := by
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
    cases h1
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_632928402561749275181254594463 : (((((((((p5 ∨ False) ∧ True) → (((True ∨ (p1 → (p1 ∨ p4))) ∨ True) → p1)) ∧ p5) ∧ (p2 → (p1 ∧ True))) ∧ (p3 → p4)) → p1) ∨ p5) ∧ True) := by
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
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h8 : ((p5 ∨ False) ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h9 := h6 h8
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h10 : ((True ∨ (p1 → (p1 ∨ p4))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h11 := h9 h10
  -- One of the premise coincides with the conclusion.
  exact h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711969014584538252066918722182 : (((((((p1 → p5) ∨ False) ∨ False) ∨ p1) ∨ (((p2 ∨ (((True → True) ∧ (p2 → True)) ∧ ((False → p5) ∧ p1))) ∨ (p5 → p3)) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215228483093338032322181628759 : ((False ∧ ((False ∧ False) ∨ p5)) ∨ ((p2 ∧ ((((p5 → p3) ∨ p2) ∨ p3) → ((p4 ∧ False) ∧ ((True ∨ p5) ∧ (False ∧ p3))))) → (p3 ∨ True))) := by
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
theorem thm_5_vars_114461150041848203937692699021 : ((((((p3 ∧ True) ∧ ((((p4 ∨ (True ∧ True)) ∧ False) ∧ p5) → True)) ∧ (True → p3)) ∨ p5) → ((p3 → p1) ∨ (p2 → False))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308627036433759417744537992076 : (p2 ∨ (((True ∨ p1) → ((((True → ((p4 ∨ (p2 ∨ (p3 ∨ (p2 → (p2 ∨ p3))))) ∨ p4)) ∧ p4) → (p2 ∨ (p2 ∨ p3))) ∧ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113635085719485126631485421813 : (((p4 → (p5 ∨ ((((p3 ∨ (True ∧ p1)) ∨ p2) ∧ (((True ∧ p4) → (True ∧ (p5 → p1))) → p1)) ∧ p5))) ∨ (p2 ∨ p2)) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192633252608296768458779210935 : (((((True → (p1 → (p4 ∨ p3))) ∨ p4) ∨ p1) → p2) → (((False ∨ ((p4 ∨ p3) ∧ (p4 ∧ (p2 ∧ p4)))) → (p3 ∨ p5)) ∨ (p4 → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148808215427428999159951980936 : (((((p1 → p2) ∧ p5) ∧ (p3 ∨ True)) → (((p2 → p1) ∧ p2) ∧ ((p2 ∧ True) ∧ (p2 ∧ (True ∧ True))))) ∨ (False → (p5 ∨ (True → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185264472329781152302491350036 : ((p1 ∧ ((p3 ∨ p3) ∨ (((p5 ∨ p2) → (p1 → p5)) ∧ p1))) ∨ (False ∨ (((p1 ∧ (False ∧ (p4 ∧ p3))) → p3) ∧ ((p1 ∨ True) ∨ False)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225028130805740536588168847977 : (((False ∧ p2) ∧ False) ∨ (((p3 → ((p5 ∨ p4) ∨ p4)) → p2) ∨ ((False ∧ ((p2 → True) → (False → p2))) → (((p2 ∧ True) → False) → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68303789561576998979987215303 : ((p3 → ((((p2 → ((p5 ∧ True) → ((p2 ∨ p3) → p5))) ∨ p4) → ((p3 → (True ∧ p1)) ∧ p4)) ∧ (p2 ∧ ((p2 → p1) ∨ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_797530072715269619849844479003 : (((p1 → ((((False ∧ p4) → (((p2 ∨ p3) ∧ ((p4 ∧ (((((p3 ∧ True) ∨ p3) ∧ p5) → p4) → p4)) ∨ p2)) ∧ p4)) ∨ p3) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56812393356111108374435086891 : ((((p4 ∨ p3) → p4) ∧ ((((p1 → (p5 ∨ True)) ∧ ((p1 → ((p5 ∨ p1) ∧ p2)) ∧ p2)) → (p3 → p5)) ∧ ((p3 ∧ p5) → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260125002400839050888375190851 : ((p2 → p1) → ((((True ∨ False) → p4) → ((p3 ∨ False) ∨ p1)) ∨ ((False ∧ (False → p5)) → ((False → (p2 ∨ (False ∨ (p2 → p4)))) → True)))) := by
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
theorem thm_5_vars_111514191237877323256538865670 : (((p5 → (((p3 ∧ p4) ∨ ((False ∨ (p4 → ((p2 ∧ p4) ∧ p1))) ∨ (p2 → (p4 ∧ (True → (True ∨ False)))))) → False)) ∧ p5) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66091300278864465035267906167 : ((p5 ∨ ((((False → p5) ∨ ((((p2 ∧ p4) ∧ (p3 ∧ (p3 ∨ p1))) ∨ p4) → (False ∧ (((False ∧ p1) ∧ p2) ∧ p4)))) ∨ False) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158027340074586469192959913209 : (((p4 ∧ ((p5 ∧ (p3 ∨ p2)) ∨ p4)) ∧ (((p1 → (p2 ∧ (p5 ∧ (False ∧ p3)))) ∨ p3) → True)) ∨ (((True ∧ p2) ∧ p3) ∨ (True ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720640661253743779637462779335 : ((((((p2 ∨ False) ∨ True) → False) → ((True → ((p5 → p1) ∧ p5)) ∨ ((((False ∨ p1) ∨ (p1 ∧ (p1 ∨ (p3 ∧ p5)))) ∨ p5) → p3))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p2 ∨ False) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165581128461698977088625386934 : ((((p2 → p5) → ((False → p5) → (True ∧ p1))) ∨ ((((False ∧ p1) → p5) ∧ True) → p1)) ∨ ((((p2 ∧ False) ∨ False) → p3) ∨ (p3 ∨ p5))) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42079986425469283495238510175 : ((((p2 → False) ∨ (p5 ∨ (False ∧ ((p4 ∧ p5) ∨ ((p4 → True) ∧ (p4 → (p4 ∧ ((False ∨ p3) ∧ ((p5 → p2) → p2))))))))) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669050392587840123586066712686 : ((((((((((False ∨ False) ∨ p1) ∧ p3) → ((p1 ∧ p4) ∧ (((True ∧ True) ∨ True) ∧ p2))) → p1) → p1) → p3) ∨ (False → (p4 ∨ p4))) ∨ False) ∧ True) := by
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
theorem thm_5_vars_647721109536278846657349837671 : ((((p5 → (p5 ∧ ((((p3 → p2) → ((((p3 ∨ ((True ∨ (True ∧ p5)) → p3)) → p1) ∨ (True ∨ p4)) → False)) → p5) ∨ p2))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248439002988673993844407646825 : ((p2 ∨ p5) ∨ ((((p5 → (p4 → (p1 ∨ p3))) ∧ ((((((p4 ∨ p3) → (p4 ∧ True)) ∧ False) → True) → (p4 ∨ p1)) → p4)) ∨ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221453908903427457325627349495 : (((False → p3) ∨ p3) ∧ ((((p3 ∧ (False → True)) ∧ (False ∨ (p3 → (p4 ∨ p2)))) → (((False ∨ p2) ∨ p3) ∨ (p5 ∨ (p3 ∨ True)))) ∨ p4)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340912664293436146756630109866 : (p2 → (((False ∨ (p5 ∨ ((p4 ∨ p3) → (p3 ∧ True)))) ∧ (p3 ∧ (((p1 ∧ p4) ∨ ((p1 ∧ False) ∨ ((p4 ∧ False) ∨ p3))) ∨ p4))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305985800656776913247511705382 : (p1 ∨ (((p5 ∨ (False ∨ p4)) ∧ False) ∨ ((True → (True ∨ ((p1 ∨ ((False ∧ (p5 → p2)) ∧ False)) ∨ p2))) ∧ ((True ∨ (True ∧ False)) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119257752872457291200334497908 : ((p2 → (p5 ∨ (p2 → (((p4 → ((p1 ∧ (True → p4)) ∧ False)) ∨ (p3 ∧ ((p2 → (True → p2)) ∧ (p1 → p1)))) → p3)))) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342181936367360786958093977638 : (p2 → ((p1 → ((p4 ∨ ((p2 → ((p1 ∨ True) → (p4 → False))) ∨ p4)) ∧ (p1 → (False ∧ (p1 → p2))))) ∨ ((True ∧ p3) → (p3 ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263401878662125270012223535379 : (True ∧ (((((False ∧ p2) ∧ True) → (p1 ∧ (p3 → p4))) → ((p2 → (((True → False) → p5) ∧ (p5 ∧ False))) → p1)) ∨ (p1 → (False → p2)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166713134731984303498505758862 : ((p3 → ((((p1 ∧ ((True → p3) → True)) ∨ p3) → p2) → ((p5 ∧ False) ∨ (p3 → p5)))) ∨ (((p1 ∧ p5) → (p4 ∧ (False ∧ True))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_768580401192993492646197505900 : (((p5 ∧ ((p5 → ((p1 ∨ p1) ∧ ((True ∧ (False ∨ False)) → ((p5 ∨ p1) → p1)))) ∨ (((p3 ∨ ((p4 → p4) ∨ p5)) ∨ p1) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_803185623693898241661999848 : ((False ∧ ((p4 → p1) ∨ ((((p4 ∨ (p2 ∨ ((False ∧ True) ∨ p4))) ∧ True) ∨ ((p4 → p4) ∧ (p3 → p5))) → (p4 ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181471285239750177964726872354 : ((p4 ∨ (((p2 ∧ (p1 ∨ p5)) ∨ True) ∨ (p3 ∧ ((True ∧ False) ∨ p2)))) → (((p4 ∨ (p4 → (p1 ∨ (p5 ∨ p4)))) ∨ p4) ∨ (True → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Conjunctions on the left can always be decomposed.
        let h6 := h5.left
        let h7 := h5.right
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h9
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h11
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h13
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- False on the left can always be used.
        apply False.elim h19
      case inr h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h21
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258400208043591367633190650038 : ((p5 ∨ p1) → (((((p4 ∧ p4) ∨ (p5 ∨ ((p2 → p1) → (True ∧ p3)))) ∧ (p2 ∨ (False ∨ p1))) ∨ ((True ∧ (False → True)) → p1)) ∨ True)) := by
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
theorem thm_5_vars_66643069856536763676472396941 : ((True → (((False ∨ p1) → (p3 ∨ ((False ∨ p1) → (False ∧ (p3 ∨ False))))) → ((p5 ∧ (False → (p5 ∧ (p2 ∨ p3)))) ∨ (p4 ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340948753815760033765901307056 : (p2 → (((p4 ∨ (True ∨ True)) ∧ ((((p1 ∧ (p4 ∨ ((p3 ∨ (p3 → ((p1 ∨ p5) ∧ p4))) ∨ p4))) ∨ False) ∧ (False → True)) → p3)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349890586215651207596761773924 : (p4 → ((p5 ∨ ((p4 ∧ ((False ∧ (((p4 ∨ True) ∧ p4) ∧ ((((p1 ∨ True) → ((p2 ∨ p2) → p3)) ∨ p3) → False))) ∧ False)) ∨ True)) ∧ True)) := by
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
theorem thm_5_vars_194256472720464947977522094865 : ((p4 → (p3 → ((p5 → p2) ∧ (p2 → (p3 ∧ p2))))) → ((((True → ((p1 ∨ p4) → p2)) ∧ p4) ∧ p4) ∨ ((p5 ∧ p1) → (p2 → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150803071021756525087664382189 : (((((((((p1 ∨ ((p4 ∧ p3) ∨ False)) ∧ False) ∨ (p2 ∨ p3)) → p5) ∨ p4) ∨ p2) ∨ (p4 ∨ p1)) ∨ p5) → ((True ∧ (p4 → False)) ∨ True)) := by
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
        -- Disjunctions on the left can always be decomposed.
        cases h4
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
      case inr h7 =>
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68597355313717641163196066882 : ((p4 → ((((p2 ∧ ((p5 ∨ p5) ∨ ((p1 ∨ (True ∧ (p4 → (True → (p1 → p2))))) ∨ (False ∨ (False ∨ p2))))) → False) ∧ p2) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122672869219635635883309412467 : ((((p5 ∨ (((p2 ∨ (False ∧ p3)) ∨ ((False ∧ p4) ∨ p2)) ∧ False)) ∨ ((p4 ∨ p1) → (p3 ∨ (p1 ∨ p4)))) → (False ∨ False)) → (p4 → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((p5 ∨ (((p2 ∨ (False ∧ p3)) ∨ ((False ∧ p4) ∨ p2)) ∧ False)) ∨ ((p4 ∨ p1) → (p3 ∨ (p1 ∨ p4)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h3
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233222091165341871168680938982 : ((p5 ∧ (p3 → p1)) → (p4 ∨ ((p2 ∧ (p3 → (False ∧ p4))) ∨ ((p1 ∧ False) → (p3 ∨ (p1 → (True → (((p1 ∧ p4) ∧ p1) → False)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166169284409229943793356574461 : ((False ∧ (True ∧ ((p3 ∨ (p3 → p2)) ∧ (((p2 ∧ p3) ∨ p3) ∧ ((p3 ∨ False) ∧ False))))) ∨ ((p4 ∧ ((p1 → p4) ∨ (True ∨ p2))) → p4)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328407675759637132661442703730 : (True → ((((p5 ∨ ((p5 ∨ p5) → ((False → ((p5 → p3) ∨ (p1 ∨ p3))) ∧ p3))) ∨ True) → p1) ∨ (p4 → ((p3 → (p5 → p5)) ∧ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h4
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325795735636260036166450401313 : (p5 ∨ (p3 ∨ ((((p5 ∧ (p5 → (p2 ∧ False))) ∧ p3) → ((p5 → ((False → (True ∨ (p4 ∧ p1))) → p1)) → (p3 ∧ (False ∧ p1)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116513000841531861516430395253 : (((p4 ∧ p4) ∧ ((p1 ∧ p2) ∨ (((((p4 ∨ p2) ∧ p4) ∨ False) ∨ ((p5 → True) ∨ (p1 ∨ (p5 ∨ p5)))) ∧ (p2 → False)))) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137535958932565120285479437097 : ((p5 ∧ (p4 ∨ ((((((p3 ∨ (p5 ∨ p2)) ∨ ((p1 ∧ p3) ∧ p4)) ∨ p5) ∧ p4) ∨ (True ∧ (p3 ∧ False))) → False))) ∨ (p4 → (True ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43487583917044673260147864501 : ((((p3 ∧ ((p1 ∨ (((True ∧ p4) ∨ (((p1 ∧ p2) → (p4 → p5)) ∨ True)) ∧ p3)) ∧ (p4 → (True ∨ (p4 ∨ False))))) ∨ False) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175346225541872509138195392523 : ((p5 ∨ ((((p3 → p3) ∧ (True → p1)) ∨ ((p1 → False) → p2)) ∧ (p2 ∧ True))) → (((p3 ∧ p5) ∧ True) → ((False ∧ False) ∨ (True → p3)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Conjunctions on the left can always be decomposed.
      let h15 := h11.left
      let h16 := h11.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h17
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h11.left
      let h20 := h11.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h21
      -- One of the premise coincides with the conclusion.
      exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682249252296460267806916365977 : (((((p4 → (((p4 ∧ p3) ∨ ((False → ((p2 ∨ p5) → True)) → p1)) → (True → p4))) → p4) ∧ (((p5 ∧ p4) ∨ p3) ∨ (True → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60324902949365291288955087819 : (((p2 → True) → (((p1 ∧ (((p4 ∨ p4) → ((False ∨ p4) ∧ p1)) → p2)) → ((p3 ∨ p2) ∧ True)) ∨ ((p2 → p3) ∧ (p2 ∨ p4)))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : ((p4 ∨ p4) → ((False ∨ p4) ∧ p1)) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h10 =>
      -- One of the premise coincides with the conclusion.
      exact h3
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h11 := h4 h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147469647154833792989282099392 : (((False ∧ (False ∨ ((p2 → (p4 → p2)) ∧ ((p3 ∨ (True → ((p1 ∨ p1) ∨ (p2 → True)))) → False)))) ∨ p1) ∨ (False → ((p3 ∧ p3) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62342166248150363749785881305 : ((p3 ∧ (((p2 ∨ p5) → ((p3 ∨ False) ∨ (p2 → ((p3 ∧ p1) ∧ (((False ∨ p2) → p2) → (True → p4)))))) ∨ (p4 → (p1 → p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_865381407034901913081617669397 : ((((((p4 ∨ (p1 → p1)) ∨ p4) ∧ (((((p2 ∧ (False → False)) → (((p2 → True) ∨ p4) ∧ p3)) → p1) → p5) ∨ (p5 → True))) → False) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p4 ∨ (p1 → p1)) ∨ p4) ∧ (((((p2 ∧ (False → False)) → (((p2 → True) ∨ p4) ∧ p3)) → p1) → p5) ∨ (p5 → True))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49521295107561211159096767329 : ((((p1 → ((True → (p3 ∨ p2)) → (((p5 ∨ (p4 ∧ (p1 ∨ (p2 ∨ p5)))) ∨ p2) ∧ True))) ∧ (p5 → p4)) → (p2 ∧ (p3 → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53007357446911225394388656150 : (((((p2 ∨ ((p5 ∧ p3) → False)) ∧ p3) ∨ (p2 ∨ (False ∧ p3))) ∧ (p3 → (False ∧ (p1 → ((p3 ∧ ((False → p3) → p2)) ∨ p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_700491132310963937426496662488 : ((((p3 ∨ (((p4 ∧ p1) → (p1 ∧ ((p2 → False) → True))) ∧ p5)) → (((p4 → ((p3 ∧ (False ∨ p2)) → (p5 → p4))) → p1) → p1)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : (p4 → ((p3 ∧ (False ∨ p2)) → (p5 → p4))) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- False on the left can always be used.
        apply False.elim h10
      case inr h11 =>
        -- One of the premise coincides with the conclusion.
        exact h5
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h12 := h2 h4
    -- One of the premise coincides with the conclusion.
    exact h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h16 : (p4 → ((p3 ∧ (False ∨ p2)) → (p5 → p4))) := by
      -- Implications on the right can always be decomposed.
      intro h17
      -- Implications on the right can always be decomposed.
      intro h18
      -- Implications on the right can always be decomposed.
      intro h19
      -- Conjunctions on the left can always be decomposed.
      let h20 := h18.left
      let h21 := h18.right
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h22 =>
        -- False on the left can always be used.
        apply False.elim h22
      case inr h23 =>
        -- One of the premise coincides with the conclusion.
        exact h17
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h24 := h2 h16
    -- One of the premise coincides with the conclusion.
    exact h24
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134808167884656360171871765758 : (((p5 ∧ (((((p3 ∧ p1) ∧ False) ∧ (True ∧ (p1 ∨ True))) ∧ p2) → (False ∨ (((p2 → p5) ∨ p5) ∧ p3)))) → p3) ∨ (p2 → (p2 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252048491948671341489002521226 : ((p4 → p1) ∨ ((p1 ∧ (False ∨ ((True → (True ∨ p2)) ∨ p1))) → (((True → (((True ∨ False) → (p3 → p1)) ∧ (p5 ∧ False))) → p3) ∨ p1))) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69485832396034369036658440625 : ((((((((p5 ∨ p4) → (True ∧ (((p1 ∧ ((p3 ∨ (p2 ∨ p3)) ∨ p1)) ∧ False) ∨ p3))) ∧ True) → p1) ∧ (p4 ∨ p3)) ∧ p3) ∧ p5) → p1) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h9 : (((p5 ∨ p4) → (True ∧ (((p1 ∧ ((p3 ∨ (p2 ∨ p3)) ∨ p1)) ∧ False) ∨ p3))) ∧ True) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h10
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h13 := h6 h9
    -- One of the premise coincides with the conclusion.
    exact h13
  case inr h14 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h15 : (((p5 ∨ p4) → (True ∧ (((p1 ∧ ((p3 ∨ (p2 ∨ p3)) ∨ p1)) ∧ False) ∨ p3))) ∧ True) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h16
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h19 := h6 h15
    -- One of the premise coincides with the conclusion.
    exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113997336241432605253281516831 : (((p4 → ((((p4 ∧ p1) ∧ (True → p3)) ∨ (p4 ∧ (p2 ∨ (True ∧ (p5 → (p4 → p3)))))) ∧ False)) ∧ ((p4 ∨ p2) ∧ True)) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38523197915293411818132340937 : ((((((p2 → (p1 ∨ p3)) ∨ p5) ∨ (p3 → (p2 → (False ∧ p3)))) → ((p4 ∨ ((p1 → False) → (p1 ∨ (p5 → False)))) ∧ True)) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311911001148842090297216288603 : (p2 ∨ (p2 ∨ (p4 ∨ ((((p5 → ((((p3 → p5) ∨ True) ∨ p1) ∨ True)) ∨ p2) ∧ p5) ∨ (p3 ∨ (p2 → (False → (p2 ∧ (False ∨ p4))))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_741848914865357102009607443196 : ((((True → p5) ∨ ((((p1 ∧ True) → ((p5 ∨ (p1 → (p2 ∨ ((True ∧ p5) ∨ False)))) → (p2 ∧ ((p5 → p3) ∧ True)))) ∨ p5) ∨ True)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_627609945206025403130291743058 : (((((((((((p5 ∨ p1) ∧ p2) ∨ p2) → (p5 ∧ False)) ∧ (False → p5)) → (((p1 ∨ p4) ∧ p3) ∨ False)) → (p4 ∨ True)) ∧ p2) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299082226338080822027584732483 : (False ∨ (((((p1 ∧ (((p2 ∨ p5) ∨ ((p5 ∨ p3) → p1)) → ((False → (p4 ∨ (True ∨ p2))) ∧ p1))) ∧ (p4 → p3)) ∧ p4) ∧ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310499631862293956034356375552 : (p2 ∨ ((((p3 ∨ False) ∨ True) → (False ∨ p5)) ∨ (((p5 ∧ True) → p5) ∨ ((p2 ∨ ((p5 → (p1 → False)) ∨ p5)) ∨ (p2 ∧ (p4 → True)))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777167926613030859105688171991 : (((p1 ∨ (((((((p4 → ((p1 ∨ (p3 → p2)) → False)) → (p3 ∨ p5)) ∨ p4) ∨ (p1 ∧ p1)) ∨ p4) ∨ p2) ∧ (False → (p2 ∧ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59495882533618370905923676980 : (((p1 → p5) ∨ (p5 → ((((p5 ∧ (p1 ∧ p2)) → (False → (p1 → ((True ∨ p3) ∨ (p1 → (p1 ∨ (p3 → p3))))))) ∧ p2) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125412750364872874257467518346 : (((p2 ∧ p1) ∧ (((((p5 ∧ (p4 ∨ ((p5 ∨ (p5 → (False ∨ p1))) ∧ False))) → (p5 ∧ p4)) → (p5 ∨ p1)) ∧ p5) → p3)) → (p3 → p3)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1775208701222947781456677928 : (((p4 ∨ ((p1 → (((p1 ∧ True) ∧ (p4 ∨ (((p3 ∧ True) → p2) ∨ p2))) ∨ p1)) → (p4 → p4))) → False) ∨ ((p2 ∨ p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317864830856618114876833407913 : (p4 ∨ (((p4 ∨ p2) ∨ ((p5 ∨ ((p2 → (p1 ∨ (p2 → (((True ∧ True) ∧ p2) ∧ (True ∧ (p3 ∧ p3)))))) ∧ p2)) ∨ (p2 → p3))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318852327416115979318901043052 : (p4 ∨ (((((p1 ∨ ((p1 ∨ (p4 → p5)) ∧ (True → (p4 → p5)))) ∨ ((p2 → p1) ∧ p5)) → (p5 ∨ p3)) ∨ p4) ∨ ((p1 ∧ False) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347383619596523500468254486126 : (p3 → (((p2 ∧ p1) ∨ ((p2 ∧ (p1 ∨ p2)) ∨ p1)) ∨ ((p5 ∨ ((p1 → (p4 ∧ (p1 ∧ p4))) ∧ (p5 ∧ ((True ∧ p3) ∨ p2)))) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184327887732079476261900222642 : ((((p3 ∨ p5) → (((p1 ∨ p1) ∧ (p4 ∧ p1)) ∧ p4)) → p3) ∨ (True ∨ (((p4 → (False ∨ ((False ∧ True) → (p3 ∧ False)))) ∨ False) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150213821587283001934052029614 : ((p2 → (((False ∧ p5) ∨ p5) ∨ ((((p1 ∨ (p5 → True)) ∧ p2) ∧ p4) ∨ (False → (p4 → (p5 ∧ p3)))))) ∨ (p4 ∧ ((True ∧ p4) → p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307195199893621632278509114781 : (p1 ∨ (p1 ∨ ((((((p2 → (p3 ∧ (p1 ∨ p1))) ∧ (p1 ∧ (p3 → p5))) ∧ p2) ∨ (p4 → p4)) ∧ (True ∧ True)) ∧ (False → (p5 ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342392065573682505190356714466 : (p2 → (((False ∨ (False ∧ ((False → p4) ∧ p4))) ∧ ((False ∧ p2) ∨ ((p4 ∧ p3) → p5))) ∨ ((False ∨ ((False → (True ∨ p2)) ∧ p2)) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707214247699671555093021840278 : (((((False → ((False → p3) ∧ (p5 ∧ p4))) → p5) ∨ ((p1 → (p3 ∧ (False ∧ p2))) ∨ (p2 → (True ∨ (((p4 ∨ p3) ∧ p4) → p2))))) ∨ p3) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340711474933121201458683296557 : (p2 → ((((p3 ∨ ((False ∨ p1) ∧ p3)) ∨ ((True ∧ p4) ∧ ((False → (p4 ∨ (False ∧ (True → True)))) → (p3 ∧ (False → p2))))) ∧ p5) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134665318505957116896239341946 : (((((p5 ∧ (p3 ∨ p1)) ∨ (p4 ∨ ((p4 → False) → True))) → ((True ∨ p1) ∧ (((False → p3) ∨ p2) ∧ p3))) → p1) ∨ (True → (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62704476605788948636646226300 : ((p4 ∧ (((((p4 ∨ (p4 ∨ (p5 ∨ p2))) → p2) → True) ∧ (((p1 ∨ (p1 → True)) ∧ (p4 → (True → p4))) ∨ (p4 → p2))) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358094232801206571384791255533 : (p5 → (p2 ∨ (((p1 → ((False ∧ ((p3 → (p4 ∧ (p1 → (((p1 ∧ p5) ∧ False) ∨ (p2 → (p1 → p2)))))) → p3)) ∨ p5)) ∨ p5) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355659168161357860561508119013 : (p5 → (((((True ∨ ((p3 ∧ p1) → ((p4 → p5) ∨ (False ∨ p2)))) → (p1 ∧ (p2 → p2))) ∧ ((p5 ∨ p5) → p4)) ∨ p3) → (p1 ∨ p3))) := by
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
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h6 : (True ∨ ((p3 ∧ p1) → ((p4 → p5) ∨ (False ∨ p2)))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h7 := h4 h6
    -- We need to get the left conjuct of h7 based on <expert-advice>.
    let h8 := h7.left
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614096688502530225911770391764 : (((((p4 ∨ ((((p5 ∨ (p2 ∧ (False ∨ p5))) → True) → True) → (((False ∨ p4) ∨ p5) → (True → p4)))) ∨ (p4 ∧ (True ∧ p4))) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_165987398393621137200157208121 : (((p1 ∧ p1) ∨ (((p3 → p5) ∨ ((False ∧ (False → p1)) ∧ (p2 → (p2 ∨ False)))) → False)) ∨ ((p3 ∧ (p3 ∧ ((p3 ∧ p3) → p2))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114429884539014577551226286093 : (((p4 ∧ (True → ((((p2 ∨ p1) ∧ p3) ∧ (p2 ∧ True)) → ((p5 ∧ (False ∧ p5)) ∨ p1)))) ∨ (p2 → ((p2 ∧ p3) → p3))) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149094028490022605773120053262 : (((True ∨ (False → p2)) → (((False ∨ (((p2 → (False → (False ∧ p5))) ∧ (p3 ∧ p5)) ∨ p3)) → p4) → False)) ∨ (((False ∨ True) → False) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_938027896977212151785104554096 : ((((True → ((p5 ∨ (p1 → p1)) ∧ p3)) ∧ (p2 → (p1 ∧ ((p1 ∧ p4) ∧ (((False ∧ ((p4 ∨ p5) ∨ (False ∧ False))) ∧ p1) → True))))) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114791336644764759593282554985 : (((((p1 → p2) ∨ (p5 → (((p1 → p4) → p2) → p2))) ∧ (False → True)) ∧ (p5 ∨ ((p3 ∨ (False ∨ (p2 → False))) ∧ p2))) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



