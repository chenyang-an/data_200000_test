variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43958713490580053399869784072 : ((((p1 ∧ (((((p4 ∨ (p2 ∧ p4)) → ((p4 ∨ (p5 ∧ p4)) ∨ p3)) ∨ (False ∨ (p4 ∨ p3))) ∨ True) ∨ p5)) ∨ (p1 ∨ p1)) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720160128807441188382131184772 : (((((True ∨ (p4 ∧ p2)) ∧ p3) → (p5 → ((((p1 ∧ p2) ∧ p1) ∨ False) ∨ (p1 → (((True ∧ p1) ∧ (p2 → p1)) ∧ (p5 ∧ True)))))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h11
    -- Implications on the right can always be decomposed.
    intro h12
    -- One of the premise coincides with the conclusion.
    exact h11
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137910593058292897954254396715 : ((p4 ∨ (((((p1 → p3) ∨ p5) ∨ False) ∨ False) → ((p3 → p1) → ((p1 ∧ ((p1 ∧ p5) ∧ p2)) ∧ (True ∧ p4))))) ∨ (p3 ∨ (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_750008001015151966941450911293 : (((True ∧ ((((p2 → (p1 ∨ p4)) ∧ (True ∧ ((p1 ∧ (p2 → p4)) ∨ p1))) → ((True ∧ ((p2 ∧ (p5 → p1)) → False)) ∧ p5)) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308599732439883568165328233367 : (p2 ∨ (((p3 ∨ (p5 ∧ p4)) → (p3 → (((((False → p4) ∧ ((p5 ∨ p4) ∧ (p5 ∨ True))) → (p4 ∨ p1)) ∨ True) ∨ (p5 → False)))) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204354505949510673528338558580 : (((p1 ∨ ((p5 ∨ False) ∧ p2)) ∧ p5) ∨ ((((True ∨ (((((p4 → (p3 ∨ p4)) ∧ p3) ∧ p2) ∧ (p2 → p5)) ∨ p2)) ∧ False) ∨ False) → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- False on the left can always be used.
      apply False.elim h4
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Conjunctions on the left can always be decomposed.
        let h10 := h8.left
        let h11 := h8.right
        -- Conjunctions on the left can always be decomposed.
        let h12 := h10.left
        let h13 := h10.right
        -- False on the left can always be used.
        apply False.elim h4
      case inr h14 =>
        -- False on the left can always be used.
        apply False.elim h4
  case inr h15 =>
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134826053860616620903412359642 : (((p1 ∨ (((p5 → (((p1 → (p4 → (((p1 → True) ∧ p1) ∧ p4))) ∨ p3) ∨ p5)) ∨ p4) → (p5 → True))) → p1) ∨ (p3 ∨ (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342404448630630122476027431639 : (p2 → ((p3 ∨ (p3 ∨ (((False ∨ (p1 ∨ (False ∨ (True → (True → p4))))) → False) ∧ p1))) ∨ ((((p5 ∧ p5) ∧ p1) → p2) ∨ (p5 → p5)))) := by
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
theorem thm_5_vars_211285913496940860011019008346 : (((p5 ∧ p1) ∨ (True ∨ p4)) ∧ ((((p1 → (p2 → (p5 ∨ p2))) → ((p1 ∧ (p1 ∧ (True ∨ p1))) ∨ (True → (True → p2)))) ∧ p5) ∨ True)) := by
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
theorem thm_5_vars_653067048012258200329796069513 : ((((True → (((False ∨ p4) → (False ∧ True)) → (((((p2 ∨ p3) ∨ p3) → p5) ∨ ((p1 ∧ p2) → (True ∨ p4))) ∨ p4))) ∧ (False ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166155498557586451739490419230 : ((False ∧ ((p2 → (((p3 ∧ p3) ∨ (p1 ∨ (p5 ∧ (p3 → p4)))) → (p1 ∨ p3))) → p2)) ∨ ((False ∨ (((p4 → p3) → p3) ∧ True)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263080299961867230539805489597 : (True ∧ (((((True ∨ ((True → True) → (False → (((p5 → True) ∧ False) ∨ True)))) → (p5 ∧ p2)) ∨ ((p5 → p5) ∧ True)) ∨ p2) ∨ (p1 ∧ p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64923226076112555132747218530 : ((p2 ∨ ((((p2 ∧ p2) → (True ∧ (False ∧ p3))) ∧ (False → ((p2 ∧ p1) → (p1 ∧ False)))) → (True → (((p1 ∧ True) → p5) ∨ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_82216323096300058917399388292 : (((((((p3 → (False → p3)) → ((False → p1) ∧ p3)) ∨ p4) ∧ (p5 ∨ ((p3 → p2) ∨ p2))) ∧ p2) ∧ ((p3 ∨ (p2 → p4)) → True)) → p2) := by
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
  cases h6
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h12 =>
        -- One of the premise coincides with the conclusion.
        exact h5
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h14 =>
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h17 =>
        -- One of the premise coincides with the conclusion.
        exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342402856062284155495210898639 : (p2 → ((False ∨ ((p4 ∧ ((True ∧ True) → (True → ((True ∧ p4) ∨ p2)))) ∨ (p3 ∨ p1))) ∨ (((p3 ∨ ((True → p3) ∨ p1)) ∨ p4) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_768034463476928649901703405329 : (((p5 ∧ ((((p4 → (p5 → p4)) ∧ (False ∧ ((((True ∧ p1) → p4) ∨ p1) ∧ (p2 ∧ True)))) ∨ (p2 ∨ (p4 → p2))) ∧ (p2 ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_605365452674297817319286560350 : ((((p3 → ((p5 → ((p1 → ((((p1 ∧ True) ∨ (p3 ∨ p3)) ∨ ((p4 ∧ p2) ∨ p4)) ∧ ((False → p4) ∧ p5))) ∧ p2)) → p2)) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151634188261233868931667491507 : ((((((False ∨ (False ∨ ((p1 ∨ ((False ∧ p2) → p5)) ∨ True))) → p4) ∧ p4) ∧ p1) ∧ ((p5 → p2) → p1)) → (p2 ∨ (True → (p3 ∨ p4)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h8
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342399585571455710798615345476 : (p2 → ((False ∧ (((p3 ∧ p5) ∧ (((p2 ∧ p1) ∨ (p2 ∧ (p3 → p3))) → False)) ∨ True)) ∨ (((p5 ∨ p4) → p2) ∨ ((False → p1) ∧ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_808021333529026664312013895258 : (((p4 → (True ∧ (((((p1 ∨ True) ∧ p3) ∨ p1) ∨ ((p1 ∧ False) → ((p3 → (((p5 → p2) ∧ p2) ∧ False)) ∨ (p3 ∧ p5)))) → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113905404388878881005199597760 : ((((p1 ∨ (((p2 ∨ p1) ∨ False) → ((((p2 → p5) ∧ (True → False)) ∧ True) ∧ (p4 ∧ False)))) → p5) ∧ ((p5 → p2) ∨ False)) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314556707883000983944438722257 : (p3 ∨ (((p3 ∨ True) → (True ∧ ((p3 → (False ∨ (False ∨ (p2 ∨ True)))) → (p3 ∨ (p2 ∨ p5))))) ∨ (p4 → (p4 ∨ ((p4 → p2) → p2))))) := by
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
theorem thm_5_vars_245098458665777675676499825134 : ((p2 ∧ True) ∨ (((p3 ∧ (p1 ∨ (((p3 ∨ False) ∧ (p2 ∧ (False → p3))) ∨ (p3 ∨ ((p5 ∧ ((p2 ∨ False) → p4)) → True))))) ∧ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774072435601392958806296079496 : (((False ∨ (((p4 → (p1 ∨ ((p2 ∨ (True ∧ p5)) → p1))) ∧ (((p2 ∨ (((True ∨ p4) → p3) → p1)) ∨ p1) ∨ p3)) ∨ (p1 → p1))) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_311758574738389822465732783306 : (p2 ∨ (False ∨ (((p5 ∧ (p2 ∨ (((True ∨ (p1 ∧ p5)) ∧ p3) ∧ p2))) → ((p4 ∨ (p1 → p1)) ∨ (p3 → p3))) ∨ (p5 ∨ (p1 ∧ False))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h16
      -- One of the premise coincides with the conclusion.
      exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_696343869177310058442767216117 : ((((p3 → (((((p2 ∧ p3) ∨ p1) ∧ p3) → (p1 ∧ True)) ∨ (p4 ∧ p5))) → ((p4 → ((p4 ∧ False) ∧ True)) → ((p4 ∧ p4) → p3))) ∨ p4) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h6
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_775466333290992341568972628485 : (((False ∨ (p3 ∧ (p2 ∧ ((p2 → False) → ((((p1 ∨ p3) → (p5 ∨ False)) → (p5 ∧ ((p4 ∧ p2) → p2))) ∨ (p2 → (p2 → p2))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135379591009300434111115714982 : ((((True → (((((p5 ∨ p2) → ((p3 ∧ p1) ∨ p1)) ∨ p1) → (p3 ∨ p2)) ∨ p5)) ∨ p2) ∨ (p2 → (p5 → p5))) ∨ (p1 ∧ (p1 ∧ p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208124828695208064196470032257 : ((((p3 ∨ True) ∨ p3) → (p4 ∧ False)) → (p3 ∨ (((False → (p3 → (((p3 ∧ p5) → ((p2 → (False ∨ True)) ∧ p2)) → p1))) ∨ p2) → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p3 ∨ True) ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118725323468775264212241552461 : ((p5 ∨ (((True → (p5 → ((p4 → False) ∧ p1))) ∨ (((False ∨ p3) → (p3 → p1)) ∧ (p5 ∧ True))) → ((p5 ∧ p5) → p1))) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165310202840847949248207664378 : (((True ∨ (p1 → (p3 ∧ ((False ∧ p5) ∨ (((p1 ∧ False) ∧ p2) ∧ p4))))) → (p1 ∧ p4)) ∨ (True ∨ (((p5 ∨ (p1 ∨ p3)) ∧ p5) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328804427077959103222722342850 : (True → ((p1 ∨ ((True ∧ ((p4 → False) ∨ p1)) ∨ (p4 ∧ p3))) ∨ ((p5 ∨ (p3 ∨ p3)) → (True ∨ ((False → (p5 ∧ p3)) → (p3 ∧ p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118463209518650649623831616164 : ((p3 ∨ ((p5 ∨ ((False ∧ p3) ∨ ((p1 ∨ (p2 ∨ p4)) → (p4 → (p5 ∧ ((p3 ∨ p1) ∨ ((p5 → False) → False))))))) ∨ True)) ∨ (p5 ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180102015201035024644975768617 : ((((p3 → ((p2 → ((p2 → (p1 → p2)) ∨ p3)) ∨ p1)) ∧ True) → False) → (((((p4 ∨ False) ∧ p2) ∨ False) ∨ p2) ∧ ((p3 ∧ p2) ∧ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p3 → ((p2 → ((p2 → (p1 → p2)) ∨ p3)) ∨ p1)) ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : ((p3 → ((p2 → ((p2 → (p1 → p2)) ∨ p3)) ∨ p1)) ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h8
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h6
  -- False on the left can always be used.
  apply False.elim h9
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h10 : ((p3 → ((p2 → ((p2 → (p1 → p2)) ∨ p3)) ∨ p1)) ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h11
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h12
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h13 := h1 h10
  -- False on the left can always be used.
  apply False.elim h13
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h14 : ((p3 → ((p2 → ((p2 → (p1 → p2)) ∨ p3)) ∨ p1)) ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h15
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h16
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h15
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h17 := h1 h14
  -- False on the left can always be used.
  apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57609265960126014779527215354 : ((((p4 → p3) ∧ True) → (p4 ∨ (p1 → (((p4 ∨ (p1 ∨ (((((p5 → (p5 ∨ False)) → p1) → p5) ∨ p5) ∧ p3))) → p5) ∨ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616268866474071173057359649054 : (((((((((True → p4) ∨ True) ∨ ((p2 ∨ p2) ∧ p1)) ∨ p5) → False) ∨ (((p2 ∧ False) → p1) ∨ (((p4 ∨ True) → p4) ∧ p3))) ∨ p3) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330769015805549061108892410125 : (True → (p1 → (True → ((p1 → (((True ∨ p4) ∧ ((p2 ∧ p2) → (p1 → p1))) ∧ ((((p5 → p5) ∧ False) ∧ False) ∨ (False ∧ p1)))) → False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179884274438513406734560597863 : ((((((p1 → True) → ((p3 ∧ p1) ∧ p2)) ∧ (p4 → p3)) ∧ True) ∨ p1) → ((p2 → ((((p1 → (p4 ∨ p5)) ∨ p4) → True) → p2)) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113559293167406577828697014306 : ((((p1 → p1) ∧ ((((p2 → p2) → (True ∨ p3)) ∨ True) → (p4 ∨ ((p4 ∧ p1) ∨ ((p4 ∧ p4) ∨ p2))))) ∨ (p1 → p2)) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172964718729458332655431769792 : ((p4 ∧ ((((p3 ∨ ((p1 ∧ p3) → True)) ∧ p1) ∧ (p1 → p3)) ∨ (p3 ∨ p2))) ∨ (True ∨ (((p1 → (True ∨ p5)) ∨ (p5 ∨ p5)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115943039447678235752053256416 : (((p1 ∨ (p2 ∨ (p2 ∧ p5))) ∨ (((p5 ∧ ((p1 → (p3 → (False → (False → p5)))) ∨ (p2 → p4))) ∧ (p5 → False)) ∨ True)) ∨ (False ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228177076184516811406765990666 : ((p5 ∧ (p2 ∧ False)) ∨ ((((p1 → False) ∨ (False ∧ p2)) ∨ p5) ∨ ((True ∨ p3) ∨ ((((p2 → False) ∨ p5) ∨ (p4 → (p1 ∨ False))) → p1)))) := by
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
theorem thm_5_vars_347583439148162285081241787381 : (p3 → ((False → (p2 ∨ (True ∧ p3))) ∧ (((p3 ∧ p5) ∨ (p5 → (p1 → p4))) → ((((False ∧ p1) ∨ p1) ∧ True) ∨ (p3 ∨ (p3 ∨ p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57744375120320703153570653500 : ((((True → p1) → p2) → (p2 → (((p3 ∧ p4) ∧ ((p3 ∨ ((((True ∧ (p4 ∧ p4)) ∧ (False ∨ p5)) ∧ p1) ∨ False)) → p5)) → p5))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  let h6 := h4.left
  let h7 := h4.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h8 : (p3 ∨ ((((True ∧ (p4 ∧ p4)) ∧ (False ∨ p5)) ∧ p1) ∨ False)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h9 := h5 h8
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670699643594373925548151238159 : ((((True ∧ ((((((p5 → p2) → (p4 ∧ ((True ∧ ((False → p5) ∨ p5)) ∧ True))) → False) → p3) ∨ p3) ∧ p4)) ∨ ((p1 → p5) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_86342285185237598135463709995 : (((((p4 → ((p3 ∧ (True ∨ p5)) ∨ p2)) ∨ True) ∨ p5) → (True ∧ (p3 ∧ (((((p4 → (p5 → True)) ∧ p2) ∧ p4) → p4) → p3)))) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p4 → ((p3 ∧ (True ∨ p5)) ∨ p2)) ∨ True) ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
theorem thm_5_vars_178792259182002361252841091399 : ((((p2 ∨ p5) ∧ True) ∨ (((p5 ∧ (p4 ∧ (p1 → True))) ∧ p4) ∨ p4)) ∨ (p5 ∨ (((p4 → p4) ∨ True) ∨ ((p1 → p4) → (False ∧ False))))) := by
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
theorem thm_5_vars_357984852666655682802010575900 : (p5 → (False ∨ (((p1 ∨ (p4 ∧ (p1 ∨ ((p1 ∨ (((True → (p5 ∨ (True → p1))) → p2) → True)) ∧ (p4 ∧ p3))))) ∨ p4) ∨ (True ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61350629001564300734331418003 : ((p1 ∧ (((p5 ∨ (p4 ∨ ((True → (p4 ∧ p1)) → p1))) ∧ ((p1 ∧ (p4 → True)) → ((p3 ∨ (True ∧ p1)) ∧ (p4 → p1)))) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185611442989389589662157495961 : ((True → ((p2 ∨ (p4 ∧ ((p4 ∧ (p2 ∧ p5)) ∨ p2))) ∨ True)) ∨ (p5 ∨ (((p5 ∧ (True ∨ False)) ∨ True) ∨ (True → ((p5 ∧ False) ∨ True))))) := by
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
theorem thm_5_vars_717811769965159508434136434597 : ((((((p3 → p1) → p5) ∧ p2) ∨ ((False → False) → ((((p5 → (((p3 ∧ p4) ∧ p4) ∧ (p1 ∨ p2))) ∨ p2) ∨ p4) → (p1 ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_801277563286208441269019688407 : (((p2 → ((((p2 ∧ (p4 → ((p1 ∧ p1) ∧ p3))) ∧ (p5 ∨ p3)) → (p2 → p5)) ∧ ((False ∨ True) → ((p3 ∧ p1) ∨ (p4 ∧ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_623812785074820242335444935190 : ((((p1 ∨ (((p1 → p5) ∨ p5) → (p2 ∨ ((((p3 → False) ∨ ((p2 ∨ (p2 ∨ (p2 ∧ p3))) → p3)) ∨ (p2 ∧ p5)) ∨ False)))) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_119633630056852345710503291221 : ((((((((p5 ∨ p5) ∧ (False → p4)) ∨ (p1 ∨ (False ∨ (False → True)))) → (((p2 → True) ∨ False) → False)) ∨ False) ∧ p4) ∧ p4) → (True ∧ p2)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : (((p5 ∨ p5) ∧ (False → p4)) ∨ (p1 ∨ (False ∨ (False → True)))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h9 := h6 h7
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : ((p2 → True) ∨ False) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h11
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h12 := h9 h10
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613407505311754745069284818858 : (((((p4 ∧ ((p2 ∨ (False → ((p5 ∧ (((p4 ∧ ((p4 → p5) ∨ False)) ∧ p2) → p4)) → p1))) ∧ (p1 → p2))) → (True ∧ p1)) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_47049688657922835536044664054 : ((((p1 ∨ (True ∧ (p2 ∧ ((p2 → True) ∧ (((True ∧ (False → (p2 ∨ p2))) ∨ False) ∨ (False → p2)))))) ∧ (True → p1)) ∨ (p4 ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118526285396081681934398272557 : ((p3 ∨ ((True → p1) → (((((p4 → True) ∧ (p1 → p3)) ∨ (((False → p1) → (True → (p4 ∧ p2))) → True)) ∨ p2) → p5))) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207022626350319880730028313391 : ((((p5 → p2) ∨ (True ∨ p2)) ∧ p4) → (((((p2 ∨ p2) → False) → p1) ∨ p2) ∨ (p5 → ((p5 ∨ p3) ∨ ((True → p5) ∧ (p5 ∧ False)))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342403503943864083559554288561 : (p2 → ((p1 ∨ (p4 ∧ ((p2 ∨ (False ∨ p3)) ∨ ((p2 ∨ ((p2 ∧ p2) → False)) ∧ False)))) ∨ (p1 → (p5 ∨ (p4 ∨ ((p5 → p3) ∨ p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_384322866304788004924012231066 : ((((((((p1 ∧ (p1 → (p5 ∨ ((p4 → (True → True)) ∧ p2)))) ∧ p3) ∨ p3) → (p1 → ((p2 ∧ True) → (True ∨ p4)))) → p2) ∨ True) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136997382441863528931506306216 : (((True ∨ p3) → ((p1 → (p3 ∧ (((p4 → p2) → ((((p5 → (True ∧ p4)) → p3) → p1) → p5)) ∨ p1))) ∨ True)) ∨ (p5 → (False ∧ True))) := by
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
theorem thm_5_vars_47805467923686078217118503199 : ((((((p4 ∨ ((p3 → p4) ∧ ((True → (p5 ∨ p3)) ∨ p2))) ∧ (((False ∨ p2) ∨ p4) → p1)) ∨ (p3 → p2)) → p1) → (p4 ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315716521517920199193741274750 : (p3 ∨ ((True → False) ∨ (((((True ∧ p1) → False) ∨ ((p3 ∨ (True ∧ p1)) ∨ (True ∨ False))) ∨ ((p2 ∨ False) ∨ p4)) ∧ (p2 → (p3 → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41322797064285650967573694664 : ((((p1 ∧ (True ∨ (p5 ∨ (((p3 → (False ∧ p1)) ∧ p4) ∧ ((False → p1) ∧ p2))))) ∧ ((p2 ∧ (p1 ∨ p5)) ∧ (True ∧ p3))) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318586309158978371317963818281 : (p4 ∨ ((((((((((p5 ∨ p5) ∧ p3) ∨ False) → p4) ∧ False) ∧ (p5 → p1)) ∧ p2) ∧ (p1 → p5)) ∨ (p4 ∨ (p5 ∨ p4))) ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263074928385669198076146976282 : (True ∧ (((p5 ∨ (((p2 ∧ (p4 ∨ True)) ∨ (p5 ∧ (p1 ∧ (False → ((p2 ∨ True) ∧ p2))))) ∧ (True ∨ (p4 → p1)))) ∧ True) ∨ (p1 ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113073649100290131546246134139 : (((p3 ∨ (p1 ∧ (((p5 → ((p2 ∧ ((p2 ∧ p5) ∨ ((p4 ∧ (True ∧ p2)) ∧ (p5 ∨ p4)))) ∧ p3)) ∨ True) ∨ True))) → False) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_665244645098618377570515260733 : ((((((p1 ∧ ((True → p1) ∨ ((p5 ∧ (True → ((True ∨ (p3 ∨ p4)) → p3))) → p1))) → (False ∧ p5)) ∧ True) ∧ ((False → p2) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50176221879818833030034684881 : ((((((((p2 ∧ p3) ∨ p2) ∨ (False ∧ False)) ∨ ((p4 → True) ∧ (p4 ∨ (False → False)))) → p2) ∧ p1) ∨ ((p2 ∧ p2) ∨ (True ∨ p4))) ∨ p5) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354617028006750992270804302147 : (p5 → ((((((p1 → False) ∨ (p5 → p3)) → (p4 ∨ (False → False))) → ((((p4 → p2) → p3) ∧ (p3 → (p2 ∧ p5))) ∨ p4)) ∨ True) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348973991880674706354015908943 : (p3 → (p4 ∨ ((p3 → (((False ∨ (True ∨ p2)) → (False ∨ ((p4 → (False → ((p2 ∨ (p5 ∨ p5)) ∨ (p2 → True)))) ∧ False))) ∨ p3)) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117795383753899596743136569315 : ((p4 ∧ ((((p4 ∨ (p5 → p4)) ∨ (p2 → True)) → p5) ∨ (p1 → ((p3 → p4) ∧ (((p5 ∧ p2) → (True ∧ p4)) → p5))))) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179566660626833232472518746745 : ((p2 → (((False ∧ (p3 ∨ (p3 ∧ p2))) → (False → p1)) → (p5 ∨ p5))) ∨ ((p1 → p1) ∨ (((p4 ∧ (True ∨ p4)) ∧ p4) ∧ (p4 ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601175626998509954237531604927 : ((((p2 ∧ ((p3 ∧ ((p3 → ((((p4 ∧ p2) ∧ p4) ∧ (p2 ∧ p1)) ∧ p4)) → ((((p1 → False) → p2) → p2) ∧ True))) ∧ p4)) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171750572617577035702310234786 : ((((False ∨ (p2 ∧ (p5 ∧ ((p4 → False) ∨ (p1 ∨ (p4 → p5)))))) ∨ p2) → p4) ∨ ((p5 ∨ (True → (False → (True ∨ (p5 ∧ p5))))) ∨ p3)) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_634088855372312594050243186201 : (((((((p2 ∧ (p3 ∧ p5)) ∧ (p1 ∧ (True → True))) ∨ ((False ∨ ((True → (p4 ∨ True)) ∧ True)) ∧ (p5 → p3))) → (p2 ∧ False)) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_820858419328332933010926338477 : (((((((((p3 → p1) ∨ (p1 → p5)) ∧ (p5 ∧ p1)) ∨ False) ∧ (p2 → (p5 → False))) ∧ ((p3 ∨ p1) → (p3 ∨ (p5 ∨ p3)))) ∧ p5) → p1) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h10.left
      let h13 := h10.right
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h10.left
      let h16 := h10.right
      -- One of the premise coincides with the conclusion.
      exact h16
  case inr h17 =>
    -- False on the left can always be used.
    apply False.elim h17
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322474359362047237527023194122 : (p5 ∨ (((True ∨ p4) ∧ (((((p4 ∨ True) ∨ p2) → ((((p3 ∨ ((p2 ∧ False) → p3)) ∧ p3) ∧ p2) ∧ (p4 → p3))) → p1) ∧ p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118497453291143990561968422890 : ((p3 ∨ (((p1 ∨ (p1 ∧ (True ∧ (p5 ∧ False)))) ∧ ((p5 → p1) ∨ p1)) ∧ ((p5 → ((p1 → p5) ∧ (p5 ∨ p3))) ∧ False))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738189095721561787969708733278 : ((((False ∧ p3) ∨ ((((p5 ∨ ((p2 ∨ (((p5 ∨ p5) → p5) ∧ p1)) → False)) ∨ (p3 ∨ (True ∨ p4))) ∨ (p2 ∨ (p5 → p2))) ∨ True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_60716264773177702299236750525 : ((True ∧ (((p4 ∧ (False ∨ p3)) ∨ (p3 ∨ p3)) ∨ (False → ((p3 → (p1 ∧ (False ∧ False))) → ((p1 → ((p2 ∧ p2) ∧ p2)) → p4))))) ∨ p1) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157055327531605687733493457977 : (((p3 ∧ (((False → (True → False)) → True) ∧ (((p5 → p4) ∨ (p1 ∨ p5)) ∨ (True ∧ p1)))) ∨ p5) ∨ ((p4 ∧ False) → ((p1 → p1) ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147690034954968859902180766458 : ((((p2 ∧ ((True ∨ p2) ∧ (((False → (p2 ∧ (p4 → True))) → True) → p1))) → ((p2 ∨ p5) ∧ p3)) → p4) ∨ ((p5 → (True ∧ True)) ∨ p1)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_799810429578386723717764344661 : (((p1 → (p3 → ((((((p3 ∨ (p5 ∨ p5)) ∨ (True ∨ p4)) ∨ (False → p4)) → p3) → p2) ∧ ((p4 ∧ (p3 → False)) ∨ (p5 ∨ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347280285296629182769097422594 : (p3 → ((((p5 ∧ p2) → (((p1 → True) ∨ False) ∧ p4)) → p5) ∨ (((p3 ∨ False) ∧ ((p3 → False) → (((p3 ∧ p4) ∧ False) → p5))) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
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
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316391370812245615734365808526 : (p3 ∨ (False ∨ ((((((False ∨ p4) ∨ p3) ∧ True) ∧ True) → p2) → ((False ∨ p1) ∨ (p3 ∨ ((((p4 → p1) ∧ p1) ∧ p4) ∨ (p4 → p4))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114571666583145855389226610010 : ((((p4 → ((p3 ∧ (((p4 ∨ p3) ∨ True) ∨ (p4 ∧ p4))) → p4)) → (p1 → p2)) ∧ (p3 ∧ (((p1 ∧ True) ∧ p1) → p1))) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260844984259259891155714051740 : ((p4 → True) → ((((p2 ∨ (p2 → (p1 ∧ (((p5 ∧ p4) ∧ (p1 ∧ (False → p5))) ∧ False)))) ∨ (p4 ∨ True)) → p2) → ((p1 → False) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p2 ∨ (p2 → (p1 ∧ (((p5 ∧ p4) ∧ (p1 ∧ (False → p5))) ∧ False)))) ∨ (p4 ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150237369983937385685570935205 : ((p3 → ((((p5 ∨ ((p2 ∨ (p5 ∧ (p4 ∨ ((p1 ∧ p2) ∧ (p5 ∧ p5))))) ∧ True)) ∨ True) ∨ p4) ∨ False)) ∨ (p1 ∧ (p4 ∧ (p3 → p3)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_598007092442674448957747651138 : (((((False ∨ (p1 ∨ True)) ∧ (p3 → ((((p2 → p2) → False) ∨ ((p2 → False) → ((p5 ∧ True) → p4))) ∧ ((False ∨ p4) ∧ p3)))) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244248384445363938284673770596 : ((False ∧ True) ∨ ((((((p4 → (p5 → p1)) → p4) ∧ (p5 ∨ (((p2 ∨ False) ∨ False) → ((p5 → p5) → (p3 ∨ True))))) ∧ True) ∨ True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215379953446945260282984031432 : ((p2 ∧ ((p1 → p5) → False)) ∨ (((((p5 ∨ ((True ∧ p3) ∧ (p3 ∧ (p5 → False)))) → p5) ∨ (False → p1)) → (p3 → False)) ∨ (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111656511904103100826846006679 : ((((False ∧ ((p3 ∨ (((p1 ∨ p1) → p2) ∨ (p4 → p1))) → (p5 ∧ (True ∨ ((p3 ∨ p4) ∧ (p3 ∧ p4)))))) ∨ p1) ∨ True) ∨ (False → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133976855765175214089067882576 : (((((p3 → (((p1 → (p3 ∨ p4)) ∨ ((((p4 ∧ p1) ∧ p3) ∧ (p5 ∨ False)) → p3)) → p1)) ∧ p2) ∧ p2) ∨ True) ∨ ((p3 ∧ True) → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166745215977721958353903687389 : ((p4 → ((((p5 → False) → (p2 ∨ p4)) → (p2 → p3)) ∨ (((p1 → p4) → p2) ∧ p2))) ∨ (p4 → ((p2 ∧ p5) ∨ ((p5 → p5) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354753111283362204305427673992 : (p5 → ((((p1 ∨ (((p3 ∧ False) ∧ p3) → (True ∨ False))) → (p2 → (True ∧ p4))) ∧ (p4 → (p4 → ((p5 → (p5 → p2)) ∧ p5)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_715931208696803876665238358750 : (((((p5 ∨ (False ∨ True)) ∨ False) ∧ (True → (p1 → (((p5 → p5) → p5) → ((p3 ∨ ((p5 → False) → p5)) ∨ (p2 → (False ∧ p2))))))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : (p5 → p5) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h5
  -- One of the premise coincides with the conclusion.
  exact h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148074031475643434670731141059 : ((((((p5 ∨ p4) → p1) ∧ (False → ((True → p5) → (((p1 ∧ p5) ∨ p1) → True)))) ∧ p2) → (p4 → p5)) ∨ (((p4 ∨ p1) ∧ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342697184572442119178183352786 : (p2 → (((True ∧ True) ∨ (p5 ∧ ((p2 ∧ (p2 → p4)) ∨ p3))) → ((p4 ∧ (((p1 ∨ False) ∧ p5) ∧ False)) ∨ (p4 → (False → (p5 ∧ p4)))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h7
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- Implications on the right can always be decomposed.
      intro h15
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h15
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h17
      -- Implications on the right can always be decomposed.
      intro h18
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h18
      -- False on the left can always be used.
      apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52021180022222818840426713982 : (((False ∨ (((p5 → ((True ∧ (False ∧ p5)) ∧ ((p5 ∧ p5) ∨ p2))) → p5) ∨ p5)) ∨ (((p3 ∧ p4) ∨ p2) ∨ ((p2 ∧ True) ∨ True))) ∨ p2) := by
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



