variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_89420910711550329972372156640 : (((p4 → (p5 ∨ p4)) ∧ (((((False ∧ p5) → (p1 → (p3 → (p5 ∧ p3)))) → p4) ∧ (((p2 ∨ p3) → p1) → p3)) ∧ (p1 → p5))) → p4) := by
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
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h8 : ((False ∧ p5) → (p1 → (p3 → (p5 ∧ p3)))) := by
    -- Implications on the right can always be decomposed.
    intro h9
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h12 := h9.left
    let h13 := h9.right
    -- False on the left can always be used.
    apply False.elim h12
    -- Conjunctions on the left can always be decomposed.
    let h14 := h9.left
    let h15 := h9.right
    -- False on the left can always be used.
    apply False.elim h14
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h16 := h6 h8
  -- One of the premise coincides with the conclusion.
  exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60998258494271244972297520804 : ((False ∧ ((((p1 ∨ (False ∧ ((False ∨ p4) → p2))) ∧ (((p4 ∨ p3) ∧ (p1 ∨ (p2 ∨ p2))) ∨ p3)) ∧ ((p3 ∧ p4) → p4)) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264560068385514669483513116437 : (True ∧ (((p1 ∨ p5) → False) ∨ (((((False ∨ p3) ∨ p1) ∨ (((True → p5) ∨ (p4 ∧ p3)) ∧ p5)) ∨ ((False ∨ (p1 → p1)) ∨ p2)) ∨ p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244414389911205958827104887276 : ((False ∧ p1) ∨ (False ∨ (((p1 ∧ p1) ∨ (True ∨ (False ∧ p5))) ∧ (((True → (p4 ∧ (p4 → (p3 → (p5 → p1))))) → True) ∨ (p2 ∧ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112166689899102292721099030569 : (((p3 ∧ ((((p2 ∨ ((p4 → p2) → (p5 ∨ p3))) ∧ (p5 → p3)) ∧ True) ∨ ((p5 ∧ (p2 ∧ p3)) ∧ (p2 → p3)))) ∨ p4) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_648199718351395912688574019670 : (((((p4 ∧ ((((p5 ∨ True) ∧ (p4 ∧ (((p5 ∨ True) ∨ ((p5 ∧ p5) ∧ p1)) ∨ (True → p3)))) → p1) ∧ p1)) ∧ False) ∧ (p3 ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_635968895837787606559284200353 : ((((((False ∧ (p1 → (((p1 ∨ (p3 ∧ p3)) ∧ ((p4 ∨ p5) → p3)) ∨ False))) → p3) ∧ ((p5 ∧ (False ∨ (False ∧ p2))) ∨ p4)) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_891678310800034637774030900442 : ((((((((False ∨ (False → (p1 ∧ p1))) → p2) ∧ ((((p2 → p1) → True) ∨ (True ∨ True)) → False)) ∧ p4) ∧ p4) ∧ (p5 → (p1 ∨ p2))) → p1) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h10 : (((p2 → p1) → True) ∨ (True ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h11 := h9 h10
  -- False on the left can always be used.
  apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315906576697574425785976342180 : (p3 ∨ (True ∧ (((p5 ∨ ((p2 ∨ False) ∧ p4)) → p4) ∨ ((p4 ∨ p5) ∨ (((p2 ∧ p4) ∨ (True → True)) ∨ ((False ∨ p1) ∧ (True → p3))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54650860974403184646884103270 : ((((((False → p4) ∧ (p2 ∨ p4)) → p2) ∨ p4) → (p2 ∧ ((((True ∧ (p5 → p2)) ∧ ((True ∨ p4) ∨ p3)) → p5) → (p3 ∨ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_686377320836137051579566262812 : ((((((p2 ∧ p2) ∨ (p3 → False)) ∧ (True ∨ (p4 → (p5 ∨ ((p4 ∨ (p4 → False)) → False))))) → (p3 → ((p2 ∧ p4) ∨ (p3 → p2)))) ∨ p4) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h13 =>
      -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
      have h14 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h12, we can now drive its conclusion.
      let h15 := h12 h14
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
      have h17 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h12, we can now drive its conclusion.
      let h18 := h12 h17
      -- False on the left can always be used.
      apply False.elim h18
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135382711989469360555132485893 : ((((((p5 ∧ (((True ∨ p4) ∧ p5) → True)) ∨ (True ∧ (True ∧ p2))) ∨ (False ∨ p5)) → False) ∨ ((False ∧ p4) → True)) ∨ ((p2 → True) ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164681949858627614135458097514 : (((((p4 → p3) ∧ (((p1 ∧ p2) ∨ False) ∨ ((False ∨ (p3 ∧ True)) ∨ p2))) ∧ p3) ∨ True) ∨ (p1 ∧ (p5 → (p1 ∨ ((True ∨ p1) ∧ p4))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52664121105245207493810731183 : (((p4 ∧ (True → (p3 ∨ (p1 ∨ ((p2 ∧ True) → (p3 ∧ (p1 ∨ p3))))))) ∨ (((((p3 ∧ p2) ∨ True) ∨ (p3 ∨ True)) ∧ p2) → p2)) ∨ p4) := by
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
  cases h2
  case inl h4 =>
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
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h11 =>
      -- One of the premise coincides with the conclusion.
      exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64935328938392466176800861698 : ((p2 ∨ ((((p5 ∨ ((True ∧ (p5 → p1)) → (p1 ∧ p3))) → True) → p4) ∧ ((False → (((p3 → p4) → p1) ∨ (True ∨ p3))) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_804197625373758242802560313992 : (((p3 → (((((((p5 ∨ True) → p2) ∨ False) ∧ (True → (p4 ∨ (False ∨ p1)))) → p4) ∨ True) ∨ (p3 ∧ ((p3 → (False ∧ p5)) ∧ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_195880975901269416729127981944 : ((True ∧ ((p4 ∧ p4) ∨ (p4 ∨ (True → True)))) ∧ (((p5 ∧ p3) → (((p2 ∨ ((p1 ∧ p1) ∨ True)) ∧ (p1 ∧ (p5 → p1))) ∨ p3)) ∧ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_776816419184712673500934457880 : (((p1 ∨ (((p3 ∧ ((p3 ∨ p4) ∨ p4)) ∨ (((p2 ∨ (p3 → (p3 ∨ False))) ∨ True) ∧ ((p5 ∨ (p1 ∨ (False ∧ p4))) → p2))) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53522993094665945601325838070 : (((p2 → ((p3 ∧ (p3 ∨ ((p1 → False) ∨ p1))) → (p4 ∧ p4))) → (((((p4 ∨ p5) → True) ∨ p5) ∧ True) → ((p4 ∧ p3) → p4))) ∨ p2) := by
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
  let h6 := h2.left
  let h7 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_660695849132396917735058948981 : (((((((p3 ∨ ((p1 → True) ∨ p1)) → ((p3 ∧ p2) → p5)) → (p5 ∧ (False ∨ (p5 → ((p4 ∧ p1) → True))))) → False) → (p5 ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184497490919843813024995354919 : (((((True ∧ p4) ∨ p3) ∨ (p4 ∧ (p5 ∨ p2))) ∨ (True ∧ False)) ∨ (p3 → (p2 → (((p5 ∨ False) ∨ (p1 → p5)) → ((p2 ∨ p4) ∨ False))))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h6 =>
      -- False on the left can always be used.
      apply False.elim h6
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683569720669037572598682562010 : ((((((p4 ∨ (((True ∨ False) ∧ ((((p4 ∨ False) ∨ p2) ∨ p3) ∧ True)) → p3)) ∧ True) ∧ p5) ∨ (((p1 ∧ p1) → p1) → (p4 ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51317588629255212714890679162 : (((p5 ∨ ((((True ∧ ((True ∧ (True → (False ∧ False))) → p1)) ∧ (False ∨ p5)) ∧ False) ∨ p3)) ∨ (((p2 ∨ (p4 ∨ p2)) ∧ p1) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299969742696211652533581178287 : (False ∨ (((True ∧ ((((True ∨ p3) ∨ ((((p5 ∨ ((p1 ∧ p3) → p4)) ∨ p4) → p5) → p4)) → p4) → p5)) ∨ (False → True)) ∧ (True ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329102951896564633657008422295 : (True → ((((False → p5) ∧ p5) ∨ False) ∨ (((p2 → p1) ∧ (False → (((p3 → p2) ∧ True) → False))) → (((True → (p3 ∧ p1)) ∨ True) ∨ p4)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324371440351791588016571941365 : (p5 ∨ (((False → p4) ∧ (p3 ∨ (False ∧ p3))) ∨ ((((p3 ∧ p2) ∨ p2) ∧ (((p2 ∧ p2) ∨ (p5 ∧ (False ∨ True))) ∨ True)) ∨ (True → True)))) := by
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
theorem thm_5_vars_47420053239009857624461839694 : (((p1 ∧ ((p3 → ((((p1 ∧ p2) ∨ p2) ∧ (p1 ∨ (((p1 ∨ p5) ∧ (True → p1)) → (p5 ∧ True)))) → p2)) → p3)) ∨ (p2 ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41401378080794190374058904998 : ((((p4 → (((False ∧ p1) ∨ ((True → ((False ∧ p1) ∨ p3)) ∧ p5)) ∧ p1)) ∧ ((p5 → (p4 ∨ (p1 → p4))) ∧ (p4 → p3))) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64092872944093184701645264412 : ((False ∨ ((False ∨ (True → ((p1 ∨ (((p1 ∧ True) → p4) ∧ p5)) ∨ p4))) → ((p4 ∨ ((p2 → p2) → ((p1 ∨ p1) ∧ p1))) ∨ True))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54302004943368117928953617843 : ((((p3 ∨ True) ∨ (((p5 ∨ p2) ∨ True) ∨ True)) ∧ ((p2 ∧ ((p3 ∧ (p5 ∧ (p5 ∨ (p1 ∧ p3)))) ∨ (p2 ∧ False))) ∨ (True ∨ p4))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231286628413666645609512542010 : (((p5 ∨ p2) ∨ False) → ((((p3 ∨ False) ∨ (True ∧ (True ∨ (p3 ∨ p5)))) → False) → ((False ∧ (False → (p2 ∧ (p5 ∧ False)))) ∧ (p3 → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h5 : ((p3 ∨ False) ∨ (True ∧ (True ∨ (p3 ∨ p5)))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h6 := h2 h5
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h8 : ((p3 ∨ False) ∨ (True ∧ (True ∨ (p3 ∨ p5)))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h9 := h2 h8
      -- False on the left can always be used.
      apply False.elim h9
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h10
  -- Implications on the right can always be decomposed.
  intro h11
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h11
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h11
  -- False on the left can always be used.
  apply False.elim h11
  -- Implications on the right can always be decomposed.
  intro h12
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h15 : ((p3 ∨ False) ∨ (True ∧ (True ∨ (p3 ∨ p5)))) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h12
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h16 := h2 h15
      -- False on the left can always be used.
      apply False.elim h16
    case inr h17 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h18 : ((p3 ∨ False) ∨ (True ∧ (True ∨ (p3 ∨ p5)))) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h12
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h19 := h2 h18
      -- False on the left can always be used.
      apply False.elim h19
  case inr h20 =>
    -- False on the left can always be used.
    apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349952307256054219351657940960 : (p4 → (((((p5 ∨ ((p5 → p2) ∧ ((p2 → True) ∨ (p3 ∨ p4)))) ∧ (p1 ∧ p4)) ∨ (((p3 ∨ False) ∨ (p1 ∨ True)) ∨ p1)) ∧ p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346964521847478052755076122944 : (p3 → ((p1 → ((p5 → p1) → ((((p1 ∧ (p3 ∧ (False ∨ (p2 → False)))) ∨ p1) → p3) → p5))) → ((True → False) → (p4 ∨ (p4 → p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226297612434255688335007426839 : (((p4 ∨ p3) ∨ p5) ∨ (p3 ∨ ((p3 ∧ p4) → ((p3 → (((p5 ∨ p1) ∨ p3) → ((p2 → (p3 ∨ False)) → (p5 ∧ (p2 ∧ p5))))) ∨ p4)))) := by
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
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789491018034021188421275800746 : (((p5 ∨ ((p3 ∧ ((p3 ∧ (p1 ∧ p2)) ∧ ((p5 → True) ∧ (p3 ∨ True)))) → (((p4 ∧ (False → ((True ∧ False) → p4))) ∧ p3) ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48574810093069398375560053563 : ((((p4 ∧ (p2 ∨ (((p3 ∧ ((((True ∧ (True ∧ p2)) ∨ p1) ∧ p4) ∨ (p5 ∨ p3))) → False) ∧ p3))) → p2) ∧ (p3 ∧ (p5 ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113430406375679619189567958404 : (((((False ∧ (((((p2 → p4) ∧ p3) ∨ (p3 ∨ (p5 ∨ False))) → (p2 ∧ True)) ∨ (p2 → p2))) ∧ False) ∨ True) ∨ (False ∨ p4)) ∨ (p3 ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_888910766393838523584674668481 : ((((((p4 → (p2 ∨ p3)) → (False ∧ (p1 ∧ p5))) ∨ (True → (((False ∧ (p5 ∧ (p5 ∨ p3))) ∨ False) → (p2 ∨ False)))) → (False ∧ True)) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p4 → (p2 ∨ p3)) → (False ∧ (p1 ∧ p5))) ∨ (True → (((False ∧ (p5 ∧ (p5 ∨ p3))) ∨ False) → (p2 ∨ False)))) := by
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
      -- False on the left can always be used.
      apply False.elim h6
    case inr h8 =>
      -- False on the left can always be used.
      apply False.elim h8
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h2
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- False on the left can always be used.
  apply False.elim h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139966902237975036595152412911 : (((False ∨ (((p5 ∧ (p3 → p3)) ∨ p3) ∨ ((p2 ∨ (p4 ∨ ((p3 ∨ False) ∧ p2))) → (False → p5)))) ∧ (p5 → False)) → ((p2 ∧ p4) ∨ True)) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h6
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
theorem thm_5_vars_151658339669119063948632354695 : ((((p5 ∨ ((p4 ∨ (False ∨ (p5 → False))) ∨ p1)) ∧ ((True ∨ p1) ∧ (p4 ∨ p4))) ∧ ((False → False) → False)) → ((p4 ∨ p5) → (p1 ∨ False))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h7.left
      let h10 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h12 =>
          -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
          have h13 : (False → False) := by
            -- Implications on the right can always be decomposed.
            intro h14
            -- False on the left can always be used.
            apply False.elim h14
          -- We have shown the premise of h5, we can now drive its conclusion.
          let h15 := h5 h13
          -- False on the left can always be used.
          apply False.elim h15
        case inr h16 =>
          -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
          have h17 : (False → False) := by
            -- Implications on the right can always be decomposed.
            intro h18
            -- False on the left can always be used.
            apply False.elim h18
          -- We have shown the premise of h5, we can now drive its conclusion.
          let h19 := h5 h17
          -- False on the left can always be used.
          apply False.elim h19
      case inr h20 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h21 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h20
        case inr h22 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h20
    case inr h23 =>
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h24 =>
        -- Disjunctions on the left can always be decomposed.
        cases h24
        case inl h25 =>
          -- Conjunctions on the left can always be decomposed.
          let h26 := h7.left
          let h27 := h7.right
          -- Disjunctions on the left can always be decomposed.
          cases h26
          case inl h28 =>
            -- Disjunctions on the left can always be decomposed.
            cases h27
            case inl h29 =>
              -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
              have h30 : (False → False) := by
                -- Implications on the right can always be decomposed.
                intro h31
                -- False on the left can always be used.
                apply False.elim h31
              -- We have shown the premise of h5, we can now drive its conclusion.
              let h32 := h5 h30
              -- False on the left can always be used.
              apply False.elim h32
            case inr h33 =>
              -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
              have h34 : (False → False) := by
                -- Implications on the right can always be decomposed.
                intro h35
                -- False on the left can always be used.
                apply False.elim h35
              -- We have shown the premise of h5, we can now drive its conclusion.
              let h36 := h5 h34
              -- False on the left can always be used.
              apply False.elim h36
          case inr h37 =>
            -- Disjunctions on the left can always be decomposed.
            cases h27
            case inl h38 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h37
            case inr h39 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h37
        case inr h40 =>
          -- Disjunctions on the left can always be decomposed.
          cases h40
          case inl h41 =>
            -- False on the left can always be used.
            apply False.elim h41
          case inr h42 =>
            -- Conjunctions on the left can always be decomposed.
            let h43 := h7.left
            let h44 := h7.right
            -- Disjunctions on the left can always be decomposed.
            cases h43
            case inl h45 =>
              -- Disjunctions on the left can always be decomposed.
              cases h44
              case inl h46 =>
                -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
                have h47 : (False → False) := by
                  -- Implications on the right can always be decomposed.
                  intro h48
                  -- False on the left can always be used.
                  apply False.elim h48
                -- We have shown the premise of h5, we can now drive its conclusion.
                let h49 := h5 h47
                -- False on the left can always be used.
                apply False.elim h49
              case inr h50 =>
                -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
                have h51 : (False → False) := by
                  -- Implications on the right can always be decomposed.
                  intro h52
                  -- False on the left can always be used.
                  apply False.elim h52
                -- We have shown the premise of h5, we can now drive its conclusion.
                let h53 := h5 h51
                -- False on the left can always be used.
                apply False.elim h53
            case inr h54 =>
              -- Disjunctions on the left can always be decomposed.
              cases h44
              case inl h55 =>
                -- Show the left disjunct based on <expert-advice>.
                apply Or.inl
                -- One of the premise coincides with the conclusion.
                exact h54
              case inr h56 =>
                -- Show the left disjunct based on <expert-advice>.
                apply Or.inl
                -- One of the premise coincides with the conclusion.
                exact h54
      case inr h57 =>
        -- Conjunctions on the left can always be decomposed.
        let h58 := h7.left
        let h59 := h7.right
        -- Disjunctions on the left can always be decomposed.
        cases h58
        case inl h60 =>
          -- Disjunctions on the left can always be decomposed.
          cases h59
          case inl h61 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h57
          case inr h62 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h57
        case inr h63 =>
          -- Disjunctions on the left can always be decomposed.
          cases h59
          case inl h64 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h63
          case inr h65 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h63
  case inr h66 =>
    -- Conjunctions on the left can always be decomposed.
    let h67 := h1.left
    let h68 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h69 := h67.left
    let h70 := h67.right
    -- Disjunctions on the left can always be decomposed.
    cases h69
    case inl h71 =>
      -- Conjunctions on the left can always be decomposed.
      let h72 := h70.left
      let h73 := h70.right
      -- Disjunctions on the left can always be decomposed.
      cases h72
      case inl h74 =>
        -- Disjunctions on the left can always be decomposed.
        cases h73
        case inl h75 =>
          -- We want to use the implication h68 based on <expert-advice>. So we show its premise.
          have h76 : (False → False) := by
            -- Implications on the right can always be decomposed.
            intro h77
            -- False on the left can always be used.
            apply False.elim h77
          -- We have shown the premise of h68, we can now drive its conclusion.
          let h78 := h68 h76
          -- False on the left can always be used.
          apply False.elim h78
        case inr h79 =>
          -- We want to use the implication h68 based on <expert-advice>. So we show its premise.
          have h80 : (False → False) := by
            -- Implications on the right can always be decomposed.
            intro h81
            -- False on the left can always be used.
            apply False.elim h81
          -- We have shown the premise of h68, we can now drive its conclusion.
          let h82 := h68 h80
          -- False on the left can always be used.
          apply False.elim h82
      case inr h83 =>
        -- Disjunctions on the left can always be decomposed.
        cases h73
        case inl h84 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h83
        case inr h85 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h83
    case inr h86 =>
      -- Disjunctions on the left can always be decomposed.
      cases h86
      case inl h87 =>
        -- Disjunctions on the left can always be decomposed.
        cases h87
        case inl h88 =>
          -- Conjunctions on the left can always be decomposed.
          let h89 := h70.left
          let h90 := h70.right
          -- Disjunctions on the left can always be decomposed.
          cases h89
          case inl h91 =>
            -- Disjunctions on the left can always be decomposed.
            cases h90
            case inl h92 =>
              -- We want to use the implication h68 based on <expert-advice>. So we show its premise.
              have h93 : (False → False) := by
                -- Implications on the right can always be decomposed.
                intro h94
                -- False on the left can always be used.
                apply False.elim h94
              -- We have shown the premise of h68, we can now drive its conclusion.
              let h95 := h68 h93
              -- False on the left can always be used.
              apply False.elim h95
            case inr h96 =>
              -- We want to use the implication h68 based on <expert-advice>. So we show its premise.
              have h97 : (False → False) := by
                -- Implications on the right can always be decomposed.
                intro h98
                -- False on the left can always be used.
                apply False.elim h98
              -- We have shown the premise of h68, we can now drive its conclusion.
              let h99 := h68 h97
              -- False on the left can always be used.
              apply False.elim h99
          case inr h100 =>
            -- Disjunctions on the left can always be decomposed.
            cases h90
            case inl h101 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h100
            case inr h102 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h100
        case inr h103 =>
          -- Disjunctions on the left can always be decomposed.
          cases h103
          case inl h104 =>
            -- False on the left can always be used.
            apply False.elim h104
          case inr h105 =>
            -- Conjunctions on the left can always be decomposed.
            let h106 := h70.left
            let h107 := h70.right
            -- Disjunctions on the left can always be decomposed.
            cases h106
            case inl h108 =>
              -- Disjunctions on the left can always be decomposed.
              cases h107
              case inl h109 =>
                -- We want to use the implication h105 based on <expert-advice>. So we show its premise.
                have h110 : p5 := by
                  -- One of the premise coincides with the conclusion.
                  exact h66
                -- We have shown the premise of h105, we can now drive its conclusion.
                let h111 := h105 h110
                -- False on the left can always be used.
                apply False.elim h111
              case inr h112 =>
                -- We want to use the implication h105 based on <expert-advice>. So we show its premise.
                have h113 : p5 := by
                  -- One of the premise coincides with the conclusion.
                  exact h66
                -- We have shown the premise of h105, we can now drive its conclusion.
                let h114 := h105 h113
                -- False on the left can always be used.
                apply False.elim h114
            case inr h115 =>
              -- Disjunctions on the left can always be decomposed.
              cases h107
              case inl h116 =>
                -- Show the left disjunct based on <expert-advice>.
                apply Or.inl
                -- One of the premise coincides with the conclusion.
                exact h115
              case inr h117 =>
                -- Show the left disjunct based on <expert-advice>.
                apply Or.inl
                -- One of the premise coincides with the conclusion.
                exact h115
      case inr h118 =>
        -- Conjunctions on the left can always be decomposed.
        let h119 := h70.left
        let h120 := h70.right
        -- Disjunctions on the left can always be decomposed.
        cases h119
        case inl h121 =>
          -- Disjunctions on the left can always be decomposed.
          cases h120
          case inl h122 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h118
          case inr h123 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h118
        case inr h124 =>
          -- Disjunctions on the left can always be decomposed.
          cases h120
          case inl h125 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h124
          case inr h126 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h124



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56170351546747176825793539980 : (((p1 ∧ (True ∨ (p5 ∨ p2))) ∨ ((False ∨ p4) ∨ (True → (p3 ∨ ((p5 ∨ (p4 ∨ (p4 ∧ (False ∧ p5)))) ∨ ((p2 ∧ p3) → True)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119136390061125281150615004465 : ((p1 → (p3 ∨ (p3 ∨ ((True → ((p4 → (((p2 ∧ p4) ∨ p2) ∧ p5)) → ((p2 ∧ (False → (p2 → True))) → False))) ∨ p4)))) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185036605331730214692992227859 : (((p1 → False) ∧ (((p2 ∧ (False → p1)) ∧ p3) ∨ (p4 ∨ p5))) ∨ (p2 ∨ (False → ((((p4 ∧ (p2 ∨ False)) ∧ p3) → (p2 ∨ p5)) → True)))) := by
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
theorem thm_5_vars_54753071675854458637358380312 : ((((p2 ∧ False) ∨ ((p3 ∧ p2) ∨ (p2 ∧ True))) → (((p1 → False) ∧ ((p2 ∧ ((False ∨ p4) → p3)) → (p4 ∨ (p2 → p3)))) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201041495703114569720797798193 : ((p4 ∨ ((True → p5) → ((p1 ∧ p1) ∧ p3))) → (False ∨ (((((p5 → (p1 ∨ False)) ∧ p2) ∧ False) ∨ True) ∨ (p1 → ((p3 ∨ p4) ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748784266092973165873202562282 : ((((p4 → True) → ((p3 ∨ ((True ∧ p3) ∧ (((p1 → ((p3 → False) → (p1 ∨ (True ∧ (p1 ∨ p5))))) ∨ p1) ∨ p4))) ∧ (p2 → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339989334061557157524224832805 : (p1 → (p1 → (((p4 → (p4 ∧ ((False ∧ (p2 ∧ (p4 ∧ p1))) → True))) ∧ p2) ∨ ((p1 → p2) ∨ (((p5 → True) → p5) ∨ (p1 ∨ True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115941094377379179307213149882 : (((False ∨ (p5 ∧ (p4 ∧ p5))) ∨ (p3 → (((p1 → (p2 → (p5 → p5))) ∧ False) ∨ ((p5 ∧ (p5 ∧ p5)) ∨ (p3 ∧ p3))))) ∨ (p3 ∧ False)) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157165666670266307594402463946 : ((((((p2 ∧ (p5 ∨ (False ∨ (((True → p3) ∨ True) ∨ (p2 ∨ p5))))) ∨ p1) ∧ p4) → p5) → p2) ∨ (True → ((p4 ∧ (False ∧ False)) → False))) := by
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
  let h5 := h4.left
  let h6 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50354450581005275894891304736 : ((((False ∨ (p2 ∨ (p4 → p3))) ∨ (p5 ∧ (((p4 → (True → p5)) → p1) ∧ ((p3 → True) → p4)))) ∨ (p4 → ((False ∧ p1) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113900148798811161896856858384 : (((((p1 ∧ (((p5 ∨ p1) ∨ (p1 ∧ p5)) → ((False ∧ p1) ∨ p5))) → (p3 → (p1 ∨ p2))) → p1) ∧ ((p2 ∧ p5) → True)) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111423557900192568422325347134 : (((p4 ∨ ((((True ∨ ((False ∧ p4) → ((p5 → (p5 ∨ p5)) ∧ ((p5 ∧ False) ∧ p3)))) → p2) ∧ (True ∧ p2)) ∧ p4)) ∧ p3) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304064686918845999903677666480 : (p1 ∨ ((p1 ∨ ((((True → (p4 ∧ p2)) ∨ p5) ∨ (p2 ∨ False)) ∧ (((p5 ∧ p2) ∨ (((p5 ∧ False) ∨ (p4 ∧ False)) ∧ p1)) ∧ p1))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147869848584984301466734530872 : (((p3 → ((p5 ∧ ((((False ∨ p5) ∧ True) ∧ (p2 → p3)) ∧ (((p3 ∨ p2) → p4) ∨ p5))) → p2)) → p2) ∨ (((p2 → p2) ∧ p1) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179387815946264712240260392868 : ((p3 ∨ (((p4 ∨ p5) → (True → (((p3 ∨ p1) → p5) ∨ p3))) → p3)) ∨ (((p2 → p3) → ((False → True) ∨ (p2 ∧ (p2 → p5)))) ∨ p1)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148420223884882171773678878004 : (((((True → p5) ∧ ((p3 ∨ p1) → (False ∨ p2))) ∧ (p4 ∨ (False → p2))) → ((True → (True → p2)) → p5)) ∨ (p5 ∨ ((p3 ∨ False) ∨ p1))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h7 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h9 := h5 h8
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h11 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h12 := h5 h11
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64476347744521328675690870484 : ((p1 ∨ ((((p5 ∨ ((p4 → ((p1 ∧ (p5 ∧ p3)) ∨ p5)) ∨ ((p1 ∨ p3) ∨ p1))) → False) ∨ True) ∧ (((True ∨ p2) ∧ p3) → True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206245711767775087357898818139 : ((False ∨ ((False ∨ (p4 ∧ p2)) ∧ False)) ∨ ((False ∨ (p4 → p4)) ∨ (((True ∨ ((True → False) ∧ False)) → ((p5 ∨ p2) ∨ p2)) ∨ (p3 → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713577949694462377154485510375 : (((((((p3 → p1) ∧ p5) ∨ p4) ∧ p1) → ((((((((False → p1) → p3) ∧ p4) ∨ p4) ∧ (True ∨ False)) ∨ p2) → (p4 ∧ p2)) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178881146658589425389198377685 : (((p3 ∧ True) ∧ ((True → (((True ∨ p4) ∧ p3) ∨ False)) ∧ (False ∨ p1))) ∨ ((((p5 ∨ ((p1 ∨ p3) → False)) ∨ (False → True)) ∧ False) → p5)) := by
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
      -- False on the left can always be used.
      apply False.elim h3
    case inr h6 =>
      -- False on the left can always be used.
      apply False.elim h3
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620851362508743644708834801096 : (((((p1 ∨ True) → ((p3 ∨ (p4 → ((p1 → (p3 ∨ (p4 → ((p5 ∧ (True ∧ p2)) ∧ True)))) ∧ ((p4 ∧ p4) → False)))) ∨ p1)) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341970152661827807397645352963 : (p2 → (((p2 ∧ (p1 → (p5 ∧ (p1 → ((p2 → ((False → p5) → p4)) ∨ ((p5 ∨ (False → True)) → p4)))))) ∨ True) ∨ (p4 → (False → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166685900894319602965427085512 : ((p2 → ((False ∨ p4) ∧ ((((False → (p5 → p4)) ∧ (p2 ∧ p5)) ∨ p4) → (p1 ∨ False)))) ∨ (p3 → (p4 ∨ (((p5 ∧ p4) ∧ p1) → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313950934026500426142376469171 : (p3 ∨ (((p1 → ((p3 → ((p5 ∧ (((False ∨ False) ∧ True) ∨ (p1 → ((p5 ∨ p4) → p1)))) ∧ p4)) → (p1 → True))) → p2) ∨ (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246696607352076170743759433671 : ((p5 ∧ p4) ∨ (((((p1 ∨ p5) ∨ (p4 ∨ (p2 ∧ p3))) → p2) → (p3 ∧ (((False ∨ p3) → p5) → True))) ∨ ((False → p1) ∨ (True → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_84056891464699801890413759376 : (((((((True → ((p4 ∧ p4) ∧ p5)) ∧ True) → False) → False) ∧ (p5 ∨ (True ∨ p4))) ∧ ((True ∨ (True ∨ p1)) → ((p2 → p2) ∧ False))) → p4) := by
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
    have h7 : (True ∨ (True ∨ p1)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h8 := h3 h7
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h12 : (True ∨ (True ∨ p1)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h13 := h3 h12
      -- We need to get the right conjuct of h13 based on <expert-advice>.
      let h14 := h13.right
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- One of the premise coincides with the conclusion.
      exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_28165850776560940881959595368 : ((True ∧ (((((p1 ∧ (((((p1 ∧ (p3 ∧ True)) → (True ∨ False)) ∨ p1) → p5) ∧ p4)) ∨ ((p5 ∨ p1) → p2)) ∨ True) → p3) ∨ True)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247599736655895039712110741313 : ((False ∨ p5) ∨ (((p5 ∨ ((False → (p1 ∧ False)) → (((p2 → (False ∧ p5)) → ((p1 ∨ p5) ∧ p4)) ∨ True))) ∨ (p5 → False)) ∧ (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258929649536567128620063487042 : ((True → p2) → (p1 ∨ (((p1 → p5) → False) ∨ ((p5 → (p4 ∨ (p2 ∨ False))) ∧ (True ∧ (((False ∧ p4) ∧ (False ∧ p4)) → (p5 ∧ p5))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- False on the left can always be used.
  apply False.elim h8
  -- Conjunctions on the left can always be decomposed.
  let h10 := h5.left
  let h11 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h10.left
  let h13 := h10.right
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49084442653384702162529324125 : (((((((False → p3) → (p2 → False)) ∨ ((True ∨ True) ∧ (p3 ∨ (True → p2)))) ∧ True) ∧ (False ∨ (p4 ∧ True))) ∨ (True ∨ (p3 → p4))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42715680747365614322360744629 : (((p5 ∨ (p1 ∨ (((p4 → (p5 ∧ p5)) → (p5 ∧ (p3 ∨ (((p2 ∨ (p1 ∨ (True → p4))) → p5) ∧ (True → p2))))) ∨ p1))) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_163716705681369431644886916396 : (((True ∨ p4) → (((p2 ∨ ((False → (p3 → (True → (p4 ∧ p5)))) ∧ False)) ∨ True) ∨ p1)) ∧ (p4 ∨ (((False ∨ (False → p5)) ∨ p5) ∨ p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
    -- True on the right can always be proven directly.
    apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175948353993439354782419229421 : (((False ∨ (((p5 ∨ ((p3 ∨ p2) ∨ p2)) ∨ p4) ∧ (False ∧ p5))) ∨ True) ∧ ((p4 ∨ (p5 → (False ∨ (p3 ∧ True)))) ∨ ((p2 ∨ True) ∨ p1))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136072039239720688610586061765 : ((((True ∨ p2) ∨ ((p4 → False) → (p2 ∧ p4))) ∧ (p2 ∨ (((p1 ∧ p1) ∧ (((True ∧ False) → p4) ∧ p3)) ∨ p5))) ∨ (p3 → (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_779275766802638036568537149872 : (((p2 ∨ (((p2 ∨ p3) → (p2 ∨ (((p3 → (((p2 ∨ p5) ∨ (p2 ∨ p2)) ∧ (p2 ∨ (True → p5)))) ∧ p3) ∧ (p1 → False)))) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671136565950598201211700831672 : ((((p2 ∨ (((((p2 ∨ p5) → ((p5 ∧ (p3 ∧ ((p2 ∧ p5) → p1))) ∧ p5)) → p4) ∨ (p3 ∨ p5)) ∧ p3)) ∨ (False → (False ∧ p1))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133977026413310270152644398479 : ((((((((((((p1 ∧ p1) → p4) ∨ p1) ∧ True) ∨ (p1 ∧ p3)) ∨ (p4 → p4)) ∧ p1) ∧ p2) ∨ p3) ∧ p3) ∨ p5) ∨ ((p1 ∧ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119522964885851844132591075901 : ((p5 → ((((p4 ∨ True) → p5) → (p2 ∨ (((p3 ∧ ((((p1 ∧ p2) ∧ p2) ∧ p1) ∨ False)) ∧ False) ∨ (p1 ∨ p5)))) ∨ p5)) ∨ (True ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624902922096120376428146949368 : ((((p5 ∨ ((((p3 ∨ True) → p1) ∨ p1) → (((True → (p2 ∨ p5)) ∧ ((p3 ∨ p1) ∧ False)) ∨ (False ∧ (p3 ∧ (p5 → False)))))) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_3055110383381211551747481186 : ((True ∧ True) ∧ ((((((p2 → (p1 ∧ p3)) ∨ (p5 ∧ p3)) ∨ p3) → ((True ∧ (p3 ∨ (p3 ∧ True))) ∧ p1)) ∨ (False ∧ False)) ∨ True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_88237212241375019824997155023 : (((True ∨ (p2 → (p4 ∧ p4))) ∧ (((((p1 ∨ p1) ∨ (p4 ∨ ((p2 → p2) → p3))) ∨ (p3 ∨ (p1 → p1))) ∧ p3) ∧ (True → p2))) → p2) := by
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
    cases h7
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
          have h12 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h6, we can now drive its conclusion.
          let h13 := h6 h12
          -- One of the premise coincides with the conclusion.
          exact h13
        case inr h14 =>
          -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
          have h15 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h6, we can now drive its conclusion.
          let h16 := h6 h15
          -- One of the premise coincides with the conclusion.
          exact h16
      case inr h17 =>
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h18 =>
          -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
          have h19 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h6, we can now drive its conclusion.
          let h20 := h6 h19
          -- One of the premise coincides with the conclusion.
          exact h20
        case inr h21 =>
          -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
          have h22 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h6, we can now drive its conclusion.
          let h23 := h6 h22
          -- One of the premise coincides with the conclusion.
          exact h23
    case inr h24 =>
      -- Disjunctions on the left can always be decomposed.
      cases h24
      case inl h25 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h26 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h27 := h6 h26
        -- One of the premise coincides with the conclusion.
        exact h27
      case inr h28 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h29 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h30 := h6 h29
        -- One of the premise coincides with the conclusion.
        exact h30
  case inr h31 =>
    -- Conjunctions on the left can always be decomposed.
    let h32 := h3.left
    let h33 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h34 := h32.left
    let h35 := h32.right
    -- Disjunctions on the left can always be decomposed.
    cases h34
    case inl h36 =>
      -- Disjunctions on the left can always be decomposed.
      cases h36
      case inl h37 =>
        -- Disjunctions on the left can always be decomposed.
        cases h37
        case inl h38 =>
          -- We want to use the implication h33 based on <expert-advice>. So we show its premise.
          have h39 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h33, we can now drive its conclusion.
          let h40 := h33 h39
          -- One of the premise coincides with the conclusion.
          exact h40
        case inr h41 =>
          -- We want to use the implication h33 based on <expert-advice>. So we show its premise.
          have h42 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h33, we can now drive its conclusion.
          let h43 := h33 h42
          -- One of the premise coincides with the conclusion.
          exact h43
      case inr h44 =>
        -- Disjunctions on the left can always be decomposed.
        cases h44
        case inl h45 =>
          -- We want to use the implication h33 based on <expert-advice>. So we show its premise.
          have h46 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h33, we can now drive its conclusion.
          let h47 := h33 h46
          -- One of the premise coincides with the conclusion.
          exact h47
        case inr h48 =>
          -- We want to use the implication h33 based on <expert-advice>. So we show its premise.
          have h49 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h33, we can now drive its conclusion.
          let h50 := h33 h49
          -- One of the premise coincides with the conclusion.
          exact h50
    case inr h51 =>
      -- Disjunctions on the left can always be decomposed.
      cases h51
      case inl h52 =>
        -- We want to use the implication h33 based on <expert-advice>. So we show its premise.
        have h53 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h33, we can now drive its conclusion.
        let h54 := h33 h53
        -- One of the premise coincides with the conclusion.
        exact h54
      case inr h55 =>
        -- We want to use the implication h33 based on <expert-advice>. So we show its premise.
        have h56 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h33, we can now drive its conclusion.
        let h57 := h33 h56
        -- One of the premise coincides with the conclusion.
        exact h57



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321356750022408061509097983620 : (p4 ∨ (True → ((p4 ∨ ((((p4 → False) → p1) ∨ p4) → (p4 → (True ∧ (p5 ∨ ((p2 ∧ ((p4 ∨ (p5 → p3)) ∨ p1)) ∨ True)))))) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1458161199666221121117804425 : (((((p1 → ((p3 ∧ False) ∨ (((False ∨ ((False ∨ p3) ∧ p1)) ∨ p3) ∨ False))) ∧ (False ∧ p1)) ∧ (p4 ∨ False)) ∧ p3) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_687197638336845475054620746453 : ((((p5 → (((p5 ∨ ((p5 ∨ ((p4 ∨ (True ∧ p3)) → p4)) ∧ (True → p2))) ∨ p1) → p3)) → ((True ∧ p2) ∨ ((p3 ∧ p4) → p4))) ∨ p1) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50061274949378711609722432055 : ((((p1 ∨ p1) ∨ (False ∨ (((True ∨ p2) ∧ (p4 ∨ ((p5 ∨ True) ∨ True))) ∨ ((p4 ∨ p4) ∧ p3)))) ∧ (True ∨ (p2 ∧ (p2 ∨ True)))) ∨ p5) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65573810403843704887732408573 : ((p3 ∨ (p4 → ((p2 ∧ False) ∨ ((((p3 ∧ p3) → p1) ∨ (((p3 → True) ∧ ((False ∨ p3) ∧ (p3 → (p5 → True)))) ∧ p5)) ∨ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197437610228028559031384646398 : ((((p4 ∧ (p3 ∧ p3)) ∧ p2) ∧ (p4 ∧ p4)) ∨ ((((p2 ∧ False) ∧ (True ∧ (p4 → p5))) → (p1 ∨ False)) ∨ ((p1 ∧ False) ∨ (p2 ∧ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205289695873900070405935654016 : (((p2 ∧ (p1 ∨ p3)) ∨ (False ∨ False)) ∨ ((p3 ∧ p3) → (((p4 → (p3 ∧ True)) → True) ∧ ((p3 → False) → (p5 ∨ ((False → False) ∨ p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h6 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h6
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159044487896305774739404620319 : ((p5 ∨ (((False ∧ ((p4 ∨ (p2 ∧ p3)) ∧ ((p3 → False) ∧ (p4 ∧ p2)))) ∨ (p4 ∨ p3)) ∨ p4)) ∨ ((p4 ∧ p5) ∨ ((True ∨ False) ∨ False))) := by
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
theorem thm_5_vars_326182689605902937487529224946 : (p5 ∨ (p2 → ((((((True → (p4 → p2)) → p3) ∧ p4) ∨ True) → p3) → (((((True → p4) ∨ (p3 ∨ (True ∨ p4))) ∨ p1) ∧ p2) → p3)))) := by
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
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h8 : ((((True → (p4 → p2)) → p3) ∧ p4) ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h9 := h2 h8
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h14 : ((((True → (p4 → p2)) → p3) ∧ p4) ∨ True) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h15 := h2 h14
          -- One of the premise coincides with the conclusion.
          exact h15
        case inr h16 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h17 : ((((True → (p4 → p2)) → p3) ∧ p4) ∨ True) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h18 := h2 h17
          -- One of the premise coincides with the conclusion.
          exact h18
  case inr h19 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h20 : ((((True → (p4 → p2)) → p3) ∧ p4) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h21 := h2 h20
    -- One of the premise coincides with the conclusion.
    exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205946900019646671347929178467 : ((False ∧ (p4 ∧ ((p4 ∨ p5) ∧ p3))) ∨ (p2 → ((p2 ∧ True) ∨ (((p3 ∧ (p2 ∧ p3)) ∧ ((p5 → False) → (p3 ∧ (p5 ∧ p5)))) ∧ True)))) := by
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
theorem thm_5_vars_635896250676102248805672140308 : (((((p4 ∨ (((p1 ∨ (p3 ∨ p5)) ∨ p4) → (((p4 ∨ (p5 ∨ p2)) ∨ (p5 → p5)) ∨ p2))) → ((False ∨ p2) ∧ (p2 ∨ p4))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113266418115002411541826231518 : ((((p2 ∨ (((p5 → ((p1 → (False → p5)) ∧ p5)) → p3) ∨ ((True → p2) ∧ True))) ∨ (True ∧ (False ∧ p4))) ∧ (True → False)) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256849684390622672511372591733 : ((p1 ∨ p3) → ((p2 → (p4 → (p5 ∨ p3))) → (p2 → (((p2 → (True → p5)) → (False ∨ (p5 ∧ True))) ∨ (p2 ∨ ((p2 ∨ True) ∨ p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171913175995587193898533530756 : (((p2 → (p1 → ((p5 → p5) → (True → (p4 ∨ ((p4 → False) → p1)))))) → p4) ∨ (True ∨ ((((p5 ∧ True) ∨ (p1 ∧ p2)) ∨ p2) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217526060882536565384824843237 : ((((p1 → p3) ∧ True) → p2) → ((p2 → False) ∨ (False ∨ (p5 ∨ (p3 ∨ (((((p4 ∧ p2) ∧ ((p3 → p2) ∧ True)) ∧ True) → p2) ∨ True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308393310306225496932934772667 : (p2 ∨ ((((p1 ∨ p3) ∨ (((False ∨ (p2 ∨ p5)) → (((p1 ∧ p2) ∨ (p4 ∧ p2)) → ((p1 ∨ p3) ∧ p2))) ∨ (True ∧ p3))) ∨ True) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313155466413608940802399213950 : (p3 ∨ (((((False ∨ p5) ∧ p3) ∨ (False ∧ ((p4 ∧ True) ∨ (p5 → p4)))) ∧ ((p3 ∧ p4) ∧ (p4 ∨ (True ∨ ((True ∨ p3) ∧ p5))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191633975317356426784762289922 : ((p4 ∧ (((False → (p5 → p1)) → (p1 → p4)) ∨ p2)) ∨ (((False ∧ (p3 ∨ True)) → ((((p5 → (False ∨ p2)) ∨ p2) ∧ p2) ∧ p5)) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_664970936866200540597541641177 : ((((p3 → (p4 ∨ ((((False ∧ (((False → (True → p2)) ∧ p1) ∧ False)) → (p3 ∨ (p5 → False))) ∨ (p2 ∨ p1)) → p2))) → (p1 ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



