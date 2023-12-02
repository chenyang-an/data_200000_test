variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_586083385523371820589237518093 : ((((((p4 ∨ ((p1 → p4) ∧ (((False → (p1 → ((p4 → False) ∧ p3))) ∧ p4) → p1))) ∧ ((p4 → True) ∨ (True ∧ p3))) ∧ p2) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208708728429069713063196868382 : ((p1 ∧ (((p2 ∨ True) ∧ p3) ∧ p3)) → (p3 ∧ ((((p5 ∧ (p4 → p1)) ∨ ((((p4 ∨ p3) → True) ∧ (p4 ∧ p5)) ∨ p1)) ∨ False) ∧ p1))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h11.left
  let h13 := h11.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h12.left
  let h15 := h12.right
  -- Disjunctions on the left can always be decomposed.
  cases h14
  case inl h16 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h17 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10
  -- Conjunctions on the left can always be decomposed.
  let h18 := h1.left
  let h19 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h20 := h19.left
  let h21 := h19.right
  -- Conjunctions on the left can always be decomposed.
  let h22 := h20.left
  let h23 := h20.right
  -- Disjunctions on the left can always be decomposed.
  cases h22
  case inl h24 =>
    -- One of the premise coincides with the conclusion.
    exact h18
  case inr h25 =>
    -- One of the premise coincides with the conclusion.
    exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727964904519671346834430532786 : ((((p3 ∨ (p2 ∧ False)) ∨ ((p2 ∧ ((p1 ∨ (p4 ∧ p1)) ∨ True)) ∧ (p3 ∨ ((p2 ∨ ((((p5 ∧ p5) → p4) → p4) ∨ p5)) ∨ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656755965322038695176082413562 : (((((False ∨ (((p5 ∨ p4) ∧ p1) → False)) ∨ (True ∧ ((False ∧ (p5 → (((p4 → (p3 ∧ p4)) ∧ True) ∨ p3))) ∨ False))) ∨ (p4 → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50203754958459192657404210380 : (((((((p2 ∧ (((p5 ∧ (p2 → p1)) ∧ (False ∨ p5)) ∨ p5)) ∧ p3) ∧ (p3 ∧ p4)) ∨ False) ∨ False) ∨ (p2 ∨ (True ∧ (p2 ∨ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39149512508139186054512149483 : ((((False ∨ p3) → ((True → ((((((p1 → p3) → (p2 ∨ p3)) ∧ p2) → False) ∧ (p3 → p1)) ∧ ((p2 ∨ p5) ∨ p1))) ∨ True)) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135229435087392456382907608056 : ((((((p5 ∧ False) ∨ (True ∧ p5)) → p1) ∨ ((True ∨ p1) → ((p4 → False) ∨ (p4 ∨ (False → p3))))) → (p2 → p3)) ∨ (False → (p5 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193304661623707643046816468834 : (((p2 ∧ (p1 ∨ p3)) ∨ ((p4 ∨ p4) ∧ (p4 ∧ True))) → (p3 → ((False ∨ ((p1 ∧ False) ∧ (False ∨ False))) ∨ (((p2 → True) ∨ p1) → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h9 =>
        -- One of the premise coincides with the conclusion.
        exact h2
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h13 =>
        -- One of the premise coincides with the conclusion.
        exact h10
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h16.left
      let h19 := h16.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h20
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h21 =>
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h22 =>
        -- One of the premise coincides with the conclusion.
        exact h2
    case inr h23 =>
      -- Conjunctions on the left can always be decomposed.
      let h24 := h16.left
      let h25 := h16.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h26
      -- Disjunctions on the left can always be decomposed.
      cases h26
      case inl h27 =>
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h28 =>
        -- One of the premise coincides with the conclusion.
        exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160370483709102267027641690875 : (((((True ∨ p1) ∧ ((True ∨ p4) ∧ (False ∧ False))) → ((p5 → True) ∨ p2)) ∧ (False ∨ (p2 ∨ p3))) → ((False → p1) ∧ ((p1 → p4) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197999010691376166743213389507 : (((True → p2) ∧ (True ∧ (p3 → (p4 ∨ False)))) ∨ (((p1 ∨ (True → p3)) ∨ (p2 ∨ ((((p2 → (p1 ∨ p2)) ∧ p1) → p3) → p5))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246058616988003738577653000923 : ((p4 ∧ False) ∨ (True → ((p3 ∨ (((p3 ∨ ((False ∧ p2) ∨ True)) ∧ ((True ∧ p2) → False)) ∧ (((p5 ∧ False) ∧ (p1 ∧ p4)) → p5))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256593595362014317917137946445 : ((p1 ∨ True) → ((p3 ∨ (True ∧ (((p4 ∧ ((True ∨ (True ∨ p2)) ∨ ((True ∨ p1) ∨ p5))) ∧ (p5 ∧ False)) ∧ p2))) ∨ (False → (True → False)))) := by
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191136768443828020737808742745 : ((((p5 ∨ p3) ∧ p5) ∨ ((p1 → (False ∨ p4)) ∨ p5)) ∨ ((False → (True ∧ ((True ∨ (p3 → (p2 → p5))) ∨ (p2 → True)))) ∨ (p1 ∧ p5))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158711621014263930841410755007 : ((p3 ∧ (((False → (p5 ∨ (((((p1 ∨ p1) ∨ p5) ∧ False) ∨ p2) ∨ p5))) ∧ (p5 ∨ p5)) → p2)) ∨ (False → (True → (False ∧ (p4 → False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209169725232718413601298653258 : ((p3 ∨ (True → (p2 ∧ (False ∨ p5)))) → ((p4 ∨ ((p5 ∧ (((p4 → True) ∨ p1) → p4)) ∨ (p3 ∨ p5))) ∨ (p5 ∨ (p2 ∧ (p1 ∧ p3))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- We need to get the right conjuct of h5 based on <expert-advice>.
    let h6 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49068981645000588800129825207 : ((((p4 ∧ ((p4 ∧ p3) → ((p2 ∧ p3) ∧ ((p4 ∧ (p4 ∨ (True → False))) ∧ (p1 ∨ p5))))) ∨ (p4 ∨ p3)) ∨ ((p5 ∧ p2) → p5)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_720801439353603166025201251041 : (((((p3 ∨ (p2 ∨ p3)) → False) → ((((((p1 → p4) → p1) → (p3 ∨ p5)) → p1) → p2) ∨ (False → (((True ∧ True) ∧ True) ∧ p2)))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_625630393318788460495183911452 : ((((p1 → (((p3 → ((p4 ∧ p2) ∨ (((p2 → ((p4 ∨ True) ∨ p3)) → p5) → p5))) ∨ ((p5 ∨ True) ∨ (p4 ∨ p4))) → p4)) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_734917155507205683735492458899 : ((((p2 ∨ p4) ∧ ((((p2 → ((False → (p3 ∨ p2)) ∨ p5)) ∧ (((((True ∨ p2) → p3) → True) → (False ∨ p4)) ∧ False)) ∧ p2) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134688997429708319110706707736 : (((((((p1 ∨ True) ∨ False) ∧ p5) ∨ p1) → (p1 ∧ ((p5 ∨ p1) → ((((False → p5) ∧ p5) ∧ p2) ∨ False)))) → p1) ∨ ((p5 ∧ p4) → p4)) := by
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
theorem thm_5_vars_111052588170278502986646544359 : ((((((p2 → (p3 → (p5 → True))) ∨ True) ∨ (p3 ∨ ((p2 → (p2 ∧ p2)) → True))) → ((p1 ∨ (p3 ∧ p4)) ∨ p1)) ∧ p4) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_243900323808902420711971442123 : ((True ∧ False) ∨ (((((((((p2 ∧ ((p4 ∨ True) ∧ p3)) ∧ False) → True) → (p4 ∧ p1)) → p1) → p3) ∨ p5) ∧ p5) ∨ ((p1 → True) ∨ p5))) := by
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
theorem thm_5_vars_707071016490826936784461808644 : ((((((p2 ∨ ((p5 ∨ p2) → p4)) ∧ p4) → p3) ∨ ((p1 ∧ p5) ∨ ((p2 → (p4 ∧ ((p3 ∨ (p4 ∧ False)) → (True → p3)))) ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165986915179253659355394276893 : (((p1 ∧ False) ∨ ((((((p4 → p3) ∧ False) ∨ ((True ∧ p1) → p1)) → p2) ∧ p2) → p3)) ∨ (((False ∧ False) ∧ (p4 → (p1 ∨ False))) → p5)) := by
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
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63386277645934124224325160682 : ((p5 ∧ (False ∨ ((p3 ∧ p1) ∧ (p5 ∨ (p1 → (((p2 ∧ p4) ∨ False) ∧ (p4 ∨ (((p3 ∨ True) ∨ (True → p4)) ∨ (True ∧ True))))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780315878728530141991757868279 : (((p2 ∨ ((((p5 ∧ (((p1 ∨ p4) ∨ p1) ∨ True)) ∨ True) ∨ (False ∧ (p5 ∧ (p3 → (False ∨ p2))))) ∨ ((p4 → (p2 ∧ p4)) ∧ p5))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319077995046247726411920389368 : (p4 ∨ (((p4 ∨ (p3 ∧ ((p5 → (True ∧ True)) ∧ (p1 ∧ ((p3 ∧ p3) ∧ ((p2 ∨ False) ∨ True)))))) ∨ False) → ((p2 ∨ (False ∧ p4)) ∨ True))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Conjunctions on the left can always be decomposed.
      let h13 := h11.left
      let h14 := h11.right
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h16 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h17 =>
          -- False on the left can always be used.
          apply False.elim h17
      case inr h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h19 =>
    -- False on the left can always be used.
    apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358228007429525083242553026619 : (p5 → (p4 ∨ ((((((p4 → p1) → p3) ∧ p4) ∧ ((p1 ∧ p1) ∨ ((True → p5) ∧ ((p5 ∨ p1) ∧ p2)))) ∨ (p3 ∨ p5)) ∨ (False ∧ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218091540467541827969085833602 : (((True → p4) ∧ (p2 → p4)) → ((((True → ((p5 → (p1 ∧ p5)) → (p4 ∧ p3))) ∨ (p3 → p4)) → p3) → (((p4 ∧ p3) ∧ p2) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148460634604377276350286934103 : (((((True ∧ p4) ∨ (p5 ∧ p4)) ∨ ((p5 → p3) → (p2 ∧ False))) ∧ (((False ∨ p3) ∨ p4) ∧ (False → True))) ∨ ((p5 → (p3 ∨ p4)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248379601259318674796587904697 : ((p2 ∨ p4) ∨ ((((p5 ∧ (p5 ∨ (p2 → p3))) ∧ (p4 ∧ (((p4 → (p4 ∧ (p5 ∧ p4))) ∨ False) → False))) ∨ ((False → p1) ∨ False)) ∨ p1)) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_651460331536112983340460894421 : (((((p1 ∨ (p4 ∨ p5)) → (((((((p1 → (p3 ∨ False)) ∨ (True → False)) → p2) ∧ p5) → False) ∧ p5) ∨ (True → True))) ∧ (p2 → True)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
  -- Implications on the right can always be decomposed.
  intro h9
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217546655951210157423224242126 : ((((False ∧ False) ∨ p1) → False) → ((p5 ∨ (p1 → ((p1 ∧ p5) ∧ p3))) ∧ (((((p2 ∧ p2) ∧ (p2 ∨ (False → False))) ∨ True) ∨ True) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((False ∧ False) ∨ p1) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- False on the left can always be used.
  apply False.elim h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : ((False ∧ False) ∨ p1) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- False on the left can always be used.
  apply False.elim h6
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_784071844495055685572534732677 : (((p3 ∨ ((p4 ∧ p2) ∨ ((True ∨ True) ∧ ((p1 ∧ p1) ∨ (p3 ∨ (p2 → (True ∨ (p1 ∧ (((False → p1) ∧ (p4 ∧ p3)) ∨ p5))))))))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_157812893197654651816191861259 : (((((p4 → (False ∨ p5)) → ((p4 ∨ (p5 ∨ True)) → p4)) → p1) → ((p1 → (True → p2)) ∧ False)) ∨ (False → ((p3 → (p3 ∧ p4)) ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167099832369253338903142880037 : (((((p5 → (False ∧ p3)) ∨ ((False → (p1 ∨ (p4 → p2))) → p1)) ∨ (p1 → p1)) ∨ p5) → ((p1 ∧ ((p2 ∨ p5) ∨ p1)) ∨ (True ∨ False))) := by
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
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698691290063709149627588617435 : (((((p1 ∧ p5) ∧ (((((p1 ∧ p1) ∧ p2) ∨ p5) → p5) ∧ p2)) ∨ (p4 ∨ (((p4 ∧ (True → (p5 ∧ p3))) ∧ p3) → (p3 ∨ p1)))) ∨ p4) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348803301166617610358981239240 : (p3 → (p1 ∨ ((((p2 ∨ ((p5 → p1) ∧ p5)) → ((p1 ∧ ((((p3 → p3) ∨ True) ∧ True) → False)) ∨ True)) ∧ p3) ∨ (p1 ∨ (p2 ∧ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306251405900726514332231693389 : (p1 ∨ ((True ∨ (p4 ∨ p1)) → ((p5 ∨ ((p3 → p2) ∨ p5)) ∨ (p4 ∨ ((True → ((p2 ∧ False) ∨ p5)) → ((False → (p5 ∨ True)) ∨ p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h9
      -- False on the left can always be used.
      apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_674615422196323149646218780554 : ((((False → ((p4 ∧ ((((p4 → False) → True) → p1) ∨ True)) ∨ (p4 ∧ ((p5 → ((p4 ∨ p4) ∨ True)) ∨ p5)))) → ((p1 ∨ p1) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_743124271840690637579578529255 : ((((p4 → p2) ∨ (((p4 ∧ p5) → ((True ∧ (p4 ∨ p3)) ∧ (False → p3))) → (((((p5 ∨ p2) → p3) → p4) ∨ (p3 ∧ p4)) ∨ True))) ∨ False) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_266202248802431870914205682555 : (True ∧ (p4 → ((p5 ∨ (True ∨ (((p3 ∨ p5) ∨ (p4 → False)) ∧ ((p3 ∨ True) → False)))) → ((p4 ∧ ((p1 ∨ (True → p4)) ∨ p4)) ∨ p1)))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h1
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h1
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h1
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h1
        case inr h11 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h1
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h1
      case inr h12 =>
        -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
        have h13 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h1
        -- We have shown the premise of h12, we can now drive its conclusion.
        let h14 := h12 h13
        -- False on the left can always be used.
        apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157013679134028419154840314733 : (((((p3 → p3) ∨ p5) → (p1 → ((p3 ∨ ((p3 → (True ∨ (p4 ∨ p4))) → p3)) ∧ p2))) ∨ False) ∨ (p5 ∨ (((p1 ∧ p3) ∨ True) ∨ p1))) := by
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
theorem thm_5_vars_56678634146364880163350807852 : ((((p3 → False) ∧ p5) ∧ ((((p5 ∨ True) ∧ ((((p2 ∨ False) ∨ p1) ∨ (p5 → (True ∧ p2))) ∧ (p3 ∧ p1))) → p2) ∨ (p3 ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351317891156997274891434948788 : (p4 → (((p2 ∨ False) → (True ∨ (p2 ∨ (False → ((p4 → False) ∨ (p4 ∨ (p3 ∧ (p1 ∨ (p4 ∧ (p5 ∨ p1)))))))))) → ((p1 → False) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50837023803540730164077202954 : (((((p5 → (True → (p1 → p3))) → (p5 ∧ (p5 ∧ ((p1 → p1) → (p5 ∨ p3))))) ∧ True) ∧ (((p1 ∧ (p3 → p1)) ∧ p3) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234644916290069189072103044158 : ((p3 → (p4 → p2)) → (((((p4 ∨ False) ∨ (False ∨ (p5 → p4))) ∨ (((p3 → True) → (p5 ∨ p4)) → (p1 ∨ (p4 ∨ p3)))) ∨ p4) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42159614344846236740580758904 : ((((p2 → p5) → (((p4 ∨ p3) ∨ p1) → (((False ∨ ((p2 ∨ p3) ∨ (False ∨ p1))) → p4) ∧ (p4 → ((p5 ∨ True) ∨ p1))))) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255576330809046068769296873671 : ((p5 ∧ p3) → (((True ∧ p3) ∨ p5) → (((p3 → p5) ∧ (p5 ∧ ((((p5 → p4) ∧ (((p3 → p1) ∧ p1) → p1)) → p2) ∨ p2))) ∨ True))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h1.left
    let h7 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h1.left
    let h10 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_775168373672307735719076315628 : (((False ∨ ((p3 ∨ p5) ∨ (p4 → (((p1 → p5) → (p4 → p5)) ∧ ((((p2 → p3) ∨ (((False ∧ p2) ∨ p1) → p4)) → False) ∧ p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606874871623297772202995694596 : (((((((((p5 → p4) ∧ (False → True)) ∨ (p2 ∧ (p1 ∨ (p3 ∨ (p1 ∨ False))))) ∧ (p1 → True)) → (p2 → (p2 ∧ p4))) ∧ True) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_148824521676459541419949436890 : (((p4 ∨ ((p4 → (p5 → p2)) ∨ False)) → ((((p3 ∨ p2) ∧ p5) → ((p4 ∧ p5) ∨ (True ∧ p4))) ∧ p5)) ∨ ((False ∧ p5) → (p1 ∨ True))) := by
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
theorem thm_5_vars_209351987018501521946038043940 : ((False → (p1 ∨ ((p5 ∧ p5) → p3))) → (p4 ∨ (((p5 → (p3 ∨ p4)) ∨ ((p3 → p5) ∨ ((((p2 ∨ p3) ∧ False) → p2) ∨ False))) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_926090230050522266920575643734 : ((((((((False ∨ (p1 ∧ (False ∨ False))) → True) ∧ True) ∧ p1) → p1) → ((p4 → (p4 ∧ (((p2 → p3) ∧ p3) ∨ (p4 ∨ p1)))) ∧ p2)) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((False ∨ (p1 ∧ (False ∨ False))) → True) ∧ True) ∧ p1) → p1) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- One of the premise coincides with the conclusion.
  exact h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217712857639929950499086887781 : (((False ∧ (p1 ∨ p5)) → p5) → (p4 ∨ (((((True ∧ ((p2 → p2) → False)) ∨ ((p3 ∨ True) ∨ (True ∧ p1))) ∧ True) → (p5 ∧ False)) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (((True ∧ ((p2 → p2) → False)) ∨ ((p3 ∨ True) ∨ (True ∧ p1))) ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_733337227507298157472411127816 : ((((p3 ∧ p5) ∧ (p2 ∨ (p2 → ((((p4 ∧ ((False ∨ p2) → p2)) ∨ p2) ∧ True) ∧ (p5 ∨ ((p2 → False) → ((True ∧ p5) ∨ p3))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655522097243962189327798560331 : (((((((p2 → (p3 ∧ (True ∧ (((p4 ∨ p2) ∨ p4) ∧ (p4 ∧ p1))))) ∧ ((p2 ∧ p5) ∧ p2)) → False) → (True → False)) ∨ (p5 ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_463058838078025822975043168663 : (((((p1 ∨ (((p3 → True) → True) ∧ False)) ∧ (((False → p3) ∧ False) ∨ (p2 ∧ p4))) ∨ (False → (True ∨ (p3 ∨ ((p2 → True) ∧ p1))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246205212953387125474346325003 : ((p4 ∧ p3) ∨ ((p2 ∧ (p5 ∧ ((p1 → (((((p5 ∧ p4) → p2) ∨ (True ∧ True)) ∧ False) → ((p1 → True) ∨ p5))) ∧ p1))) ∨ (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_710573745226199666063420532490 : ((((((p4 ∨ p4) → p3) ∧ (p3 ∨ p4)) ∧ ((((((p4 ∨ p2) ∧ (True ∨ p5)) ∨ p5) ∨ p2) → (p2 ∨ (p2 ∨ (False ∨ p1)))) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318944844622979318647707161306 : (p4 ∨ (((p4 → ((p4 ∧ p4) → ((False → True) ∨ p5))) → ((p3 ∨ ((p3 ∧ p5) → (p1 ∨ (p4 → True)))) ∧ False)) → ((p5 ∧ p5) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : (p4 → ((p4 ∧ p4) → ((False → True) ∨ p5))) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h5
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313245723595762698308463227243 : (p3 ∨ (((p4 → p5) ∨ (p4 ∨ ((((((p4 → (p3 → False)) ∧ ((p2 ∨ p1) ∨ p1)) ∧ p3) → p3) → p1) ∨ (False ∨ (p2 → True))))) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774036543080272997277615789472 : (((False ∨ ((((p4 ∧ ((False ∨ (p1 → (p5 ∨ p1))) ∧ (p3 ∨ p5))) ∧ (p2 → ((p5 ∨ p4) ∨ (p5 ∨ True)))) ∧ False) ∨ (p3 → p3))) ∨ p4) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_745742544032787510580549390450 : ((((False ∨ True) → ((((False → (p3 → (p2 ∧ ((True ∧ (p3 → (p4 ∨ ((False ∧ p3) ∨ p5)))) ∨ p4)))) → p1) ∧ (p5 ∨ p3)) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174246973794504187374626570966 : (((p5 ∨ (p3 ∧ (p4 ∨ (p4 ∨ ((p3 → p4) → (True ∧ True)))))) → (True ∨ p4)) → ((((p1 ∨ p2) ∧ (p5 ∧ p5)) ∨ p4) ∨ (p2 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_71201360840693654369804823896 : (((((p5 → p4) ∧ p5) ∧ (p4 → (p4 → ((p1 → (((p3 ∧ p3) ∧ (((p1 ∧ False) ∨ (p1 → p2)) → p4)) → p4)) ∧ False)))) ∧ p2) → False) := by
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
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h8 : p4 := by
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h9 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h10 := h6 h9
    -- One of the premise coincides with the conclusion.
    exact h10
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h11 := h5 h8
  -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
  have h12 : p4 := by
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h13 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h14 := h6 h13
    -- One of the premise coincides with the conclusion.
    exact h14
  -- We have shown the premise of h11, we can now drive its conclusion.
  let h15 := h11 h12
  -- We need to get the right conjuct of h15 based on <expert-advice>.
  let h16 := h15.right
  -- False on the left can always be used.
  apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_87413498817897436311441784657 : (((False ∨ (p1 ∧ (p1 → (p2 ∧ p4)))) ∧ (False ∨ ((True ∨ ((p1 ∧ ((True ∧ True) ∧ p1)) ∧ True)) ∨ ((p1 ∨ True) ∧ (True ∨ p5))))) → p4) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
          have h12 : p1 := by
            -- One of the premise coincides with the conclusion.
            exact h6
          -- We have shown the premise of h7, we can now drive its conclusion.
          let h13 := h7 h12
          -- We need to get the right conjuct of h13 based on <expert-advice>.
          let h14 := h13.right
          -- One of the premise coincides with the conclusion.
          exact h14
        case inr h15 =>
          -- Conjunctions on the left can always be decomposed.
          let h16 := h15.left
          let h17 := h15.right
          -- Conjunctions on the left can always be decomposed.
          let h18 := h16.left
          let h19 := h16.right
          -- Conjunctions on the left can always be decomposed.
          let h20 := h19.left
          let h21 := h19.right
          -- Conjunctions on the left can always be decomposed.
          let h22 := h20.left
          let h23 := h20.right
          -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
          have h24 : p1 := by
            -- One of the premise coincides with the conclusion.
            exact h21
          -- We have shown the premise of h7, we can now drive its conclusion.
          let h25 := h7 h24
          -- We need to get the right conjuct of h25 based on <expert-advice>.
          let h26 := h25.right
          -- One of the premise coincides with the conclusion.
          exact h26
      case inr h27 =>
        -- Conjunctions on the left can always be decomposed.
        let h28 := h27.left
        let h29 := h27.right
        -- Disjunctions on the left can always be decomposed.
        cases h28
        case inl h30 =>
          -- Disjunctions on the left can always be decomposed.
          cases h29
          case inl h31 =>
            -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
            have h32 : p1 := by
              -- One of the premise coincides with the conclusion.
              exact h30
            -- We have shown the premise of h7, we can now drive its conclusion.
            let h33 := h7 h32
            -- We need to get the right conjuct of h33 based on <expert-advice>.
            let h34 := h33.right
            -- One of the premise coincides with the conclusion.
            exact h34
          case inr h35 =>
            -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
            have h36 : p1 := by
              -- One of the premise coincides with the conclusion.
              exact h30
            -- We have shown the premise of h7, we can now drive its conclusion.
            let h37 := h7 h36
            -- We need to get the right conjuct of h37 based on <expert-advice>.
            let h38 := h37.right
            -- One of the premise coincides with the conclusion.
            exact h38
        case inr h39 =>
          -- Disjunctions on the left can always be decomposed.
          cases h29
          case inl h40 =>
            -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
            have h41 : p1 := by
              -- One of the premise coincides with the conclusion.
              exact h6
            -- We have shown the premise of h7, we can now drive its conclusion.
            let h42 := h7 h41
            -- We need to get the right conjuct of h42 based on <expert-advice>.
            let h43 := h42.right
            -- One of the premise coincides with the conclusion.
            exact h43
          case inr h44 =>
            -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
            have h45 : p1 := by
              -- One of the premise coincides with the conclusion.
              exact h6
            -- We have shown the premise of h7, we can now drive its conclusion.
            let h46 := h7 h45
            -- We need to get the right conjuct of h46 based on <expert-advice>.
            let h47 := h46.right
            -- One of the premise coincides with the conclusion.
            exact h47



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306402417524611745993882281188 : (p1 ∨ ((p1 ∧ True) ∨ ((True ∨ p1) → (((((p5 ∨ p5) → ((False ∨ p4) → False)) ∧ ((False → True) → p5)) → ((p1 ∨ p1) ∧ p2)) ∨ True)))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_144636362807177829499840305428 : (((((p3 ∧ p5) ∨ ((p3 → (p5 ∧ True)) ∧ ((p1 ∧ p3) ∨ p1))) → ((p1 → False) → p2)) → (p2 ∨ True)) ∧ (p1 → ((True → p5) ∨ p1))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147671784443938806238828453073 : (((((False ∨ (p5 → p3)) ∨ ((((p4 ∧ (p4 → p2)) → (p3 ∧ p1)) ∧ p2) ∧ False)) → (p1 ∧ True)) → p4) ∨ ((p5 ∧ (p3 ∧ False)) → p1)) := by
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
theorem thm_5_vars_147858827279998411596447653359 : (((False → (p4 ∧ (p4 → (((p4 ∨ True) → (p4 → (True ∨ ((True → p4) → (p5 ∧ p3))))) → True)))) → p3) ∨ ((p2 ∧ False) → (True → False))) := by
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
theorem thm_5_vars_428592838827899103449773687691 : (((((p4 ∨ (p1 ∧ (True ∧ ((((((p3 → False) ∧ (p4 ∧ (p5 ∧ True))) → False) ∨ (p5 ∧ p2)) ∨ p3) ∨ p4)))) → p5) ∨ (True ∨ p5)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200723547599833396757275557432 : ((p3 ∧ ((((p4 ∧ True) ∨ p2) ∧ p1) ∨ p1)) → (((p2 ∨ (p5 ∨ (p2 → p2))) → ((p3 ∨ ((p2 ∧ True) ∨ p3)) ∧ (False ∨ True))) ∨ True)) := by
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
    cases h5
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
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
theorem thm_5_vars_260883925990885674548486684927 : ((p4 → False) → (((((p1 ∧ (p1 ∧ ((p1 → ((True → p3) ∨ True)) → True))) → (p1 ∧ False)) → ((p3 ∧ p4) ∧ p3)) ∨ (False → False)) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356046798331670174502673199242 : (p5 → ((p1 ∨ ((p1 → p1) → ((p2 ∧ (p1 ∧ (p4 ∨ True))) ∧ ((p4 ∨ (p3 ∧ p5)) → (True → p4))))) ∨ ((p2 ∧ p5) ∨ (p4 → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749348335342194255413312811118 : (((True ∧ (((p3 → (False ∧ ((((False ∧ ((p1 ∨ p5) ∧ (p3 ∨ p2))) → p2) → (p5 ∨ (p3 ∧ (False ∧ True)))) ∨ p1))) ∧ p3) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_854597804497962034445558636629 : ((((((False ∨ (p4 → (p1 ∨ p5))) ∨ (p2 → (((p4 ∧ (p5 ∨ (((p5 ∨ (p2 ∨ p2)) ∨ p1) → True))) ∨ p4) ∨ p2))) ∧ True) → p1) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((False ∨ (p4 → (p1 ∨ p5))) ∨ (p2 → (((p4 ∧ (p5 ∨ (((p5 ∨ (p2 ∨ p2)) ∨ p1) → True))) ∨ p4) ∨ p2))) ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197848301481964393480481277602 : (((True → (p4 ∨ p5)) ∨ (p3 ∧ (p4 ∨ p1))) ∨ ((p2 → ((((p2 ∧ p2) → p3) ∧ ((True ∧ p4) ∧ False)) ∨ (p1 ∨ p2))) ∨ (p5 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_313126713137271031212744211731 : (p3 ∨ ((((p2 → ((p4 ∨ ((p3 ∨ True) ∨ p5)) ∧ False)) ∨ (p1 ∨ ((False ∧ p1) → (p1 ∧ p4)))) ∨ ((True ∨ p1) ∧ (p5 ∧ p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187189366087159416956375069072 : (((True ∨ False) → (((p5 ∨ p2) ∧ (p4 → True)) ∧ (False ∧ p5))) → ((True → p1) → (p3 ∨ (p2 ∨ ((p5 ∨ p4) → ((p4 ∨ True) → p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (True ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_660679842599600030619812482544 : ((((((((p2 ∧ ((((p2 → p4) → True) ∧ p1) ∨ p3)) ∨ p3) → True) → (p5 ∨ (p5 ∨ (p2 ∧ (p2 ∨ p5))))) → p2) → (p4 → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41027867329217676655854918588 : ((((((p5 → p1) ∨ ((p1 ∨ (((p1 ∨ True) → p2) ∨ p5)) → (p3 → (p4 → (p5 → True))))) ∨ (True ∨ p5)) → (False ∧ True)) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_598948214175404374757326287948 : (((((p1 ∨ p1) ∧ (((p5 → (p3 ∧ (p3 → (p4 ∧ (p3 ∧ True))))) → ((((True ∧ p1) → p3) → p3) ∨ (p5 ∧ False))) ∨ p5)) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191165406296155061181497587584 : (((p4 ∧ (p1 → p4)) ∨ ((p5 → True) → (p4 ∧ p4))) ∨ ((p4 ∧ ((True ∨ p5) ∨ p4)) ∨ ((False ∨ (((p3 ∨ True) ∧ p1) ∧ False)) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61489671500845576027385610026 : ((p1 ∧ (((p5 ∧ ((False ∧ ((False ∧ p5) ∨ (p5 ∨ (False ∨ True)))) ∨ ((True → p4) → p2))) ∨ (p3 ∧ p4)) ∨ (p2 ∨ (p5 ∨ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608592181488153840535152560182 : ((((((((p5 ∧ True) → (False ∧ (p5 → (((p1 → p4) ∧ ((p2 ∨ p1) → (p4 → p5))) → p4)))) ∨ p4) ∧ (p1 → p3)) ∨ p1) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_216216048224383996636495509860 : ((p1 → ((p5 ∨ p5) ∧ p4)) ∨ (p1 → ((p4 ∧ (((p4 → False) ∧ (((((True → p3) → p1) ∧ (p4 ∨ p4)) ∧ False) → False)) ∨ p3)) → p4))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_799631756725024239488156642125 : (((p1 → (p5 ∨ (p5 ∨ ((True ∧ ((((p2 ∧ p5) ∨ p3) → False) ∨ (p3 → p2))) ∨ ((False ∨ ((p5 → p4) ∧ False)) → (False → p1)))))) ∨ p3) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68497044813225354625610471181 : ((p3 → (p2 ∨ ((p1 → ((p1 ∧ p3) ∧ (p1 ∧ (p5 → ((((p3 → True) ∧ p3) ∧ (p2 ∨ (p3 → True))) ∧ p2))))) ∨ (p2 ∧ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153647195158021933058529192310 : ((p1 → (p3 ∧ (p1 → ((True ∧ (True → p1)) ∧ ((((p2 ∨ (p3 ∧ p2)) ∧ (p1 ∧ False)) ∧ p1) ∧ p3))))) → ((p5 ∨ p1) ∨ (p1 → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116002358139182377597563112440 : ((((p5 ∧ p1) ∧ (p5 → False)) → (True → (((p2 ∧ True) ∧ ((p4 → (False → p1)) → (p2 → (p4 ∧ False)))) ∨ (p1 ∨ p1)))) ∨ (p5 ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196976869440313504852610428434 : (((((p3 → (False ∧ p1)) ∨ p3) → p2) ∨ p5) ∨ ((p4 ∨ (p5 ∨ p4)) ∨ ((((p4 ∧ (p2 ∨ p1)) ∧ ((p5 ∧ p2) ∧ True)) ∨ True) ∨ p4))) := by
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
theorem thm_5_vars_809248213990902726538606463768 : (((p5 → (((p2 ∨ ((p3 ∧ (((p3 → (p3 → False)) ∨ p5) ∨ p5)) → p2)) → (p1 ∧ (((True → p5) ∨ p5) → (p1 ∧ True)))) ∨ p5)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_228443236763748772767851461217 : ((False ∨ (False ∨ p2)) ∨ (p3 ∨ (p2 → (p4 ∨ (False → (p3 ∨ (p5 → (((((True ∨ p3) → (False → p1)) ∨ True) → True) → (p2 ∧ p3))))))))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135409548484075859360643745979 : ((((p3 ∧ (False ∧ True)) ∧ (False ∧ ((p1 ∧ True) ∨ ((p5 → p5) ∧ ((False ∧ False) ∧ p3))))) ∨ (False → (False → True))) ∨ (p3 → (p3 ∧ p5))) := by
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
theorem thm_5_vars_782276509081466276854293893247 : (((p3 ∨ ((p4 ∧ (False ∨ (((True ∨ (p3 ∧ p1)) ∧ (((p2 ∧ (False → p1)) ∧ p1) ∨ p4)) ∧ (((p1 ∧ False) ∧ p2) → False)))) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712905669102847277748349716120 : ((((True ∧ ((p5 ∧ True) ∨ (p3 ∧ p3))) ∨ (p1 ∧ (p4 ∧ (((p3 ∧ ((p1 ∧ p5) ∧ (p4 ∧ ((p1 ∨ p5) → True)))) ∨ p2) → p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43310460414142333285822606532 : (((((((((True ∧ p4) ∧ p1) ∨ (True → p2)) ∧ ((p5 → False) ∧ p5)) ∨ (True → (((p4 → False) → False) ∨ p5))) ∨ False) ∨ p1) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193172276225664812231031610806 : (((((False ∧ p4) ∧ p1) ∨ p2) → ((False → p1) ∧ p5)) → ((True → (p5 ∧ p2)) → ((True → p1) ∨ ((True ∨ (p3 → p4)) ∧ (False → p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263154029208387786866014877889 : (True ∧ ((p1 ∧ ((((False ∨ (p4 ∧ True)) ∨ p3) → (True ∧ p1)) → ((p5 ∧ ((p1 ∨ p1) ∨ ((True ∨ p5) → p2))) ∨ p1))) ∨ (True → True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



