variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112416923917835869077754155217 : ((((p4 ∨ ((p2 ∧ ((False ∨ p1) ∧ (p2 → (((p5 ∧ p2) → (True → (p2 ∧ p4))) ∧ (p5 ∧ p3))))) ∧ p4)) ∧ p5) → False) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215813892891380552950339949077 : ((p2 ∨ ((p2 ∧ p3) ∧ p5)) ∨ (p4 ∨ ((p1 ∧ (p2 ∨ (((p2 ∧ p3) ∨ p1) ∨ ((p2 ∧ (False ∧ (False → (p5 ∧ p4)))) ∧ p3)))) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50453162479859395051827419080 : (((p3 ∨ (((((p1 → ((True ∧ p4) → p2)) ∨ p4) ∨ p3) ∨ p2) ∧ (((True ∧ False) ∧ p1) ∨ p4))) ∨ ((p3 ∧ (p5 ∨ p1)) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_81091614289067664832316478338 : ((((p2 ∧ (True → p3)) ∧ (((p5 ∧ True) ∨ p1) ∧ ((((p4 → True) ∨ (p1 ∧ True)) ∨ (p2 ∧ p3)) ∧ p1))) ∧ ((False ∧ p4) → p2)) → p3) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h9.left
    let h14 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h17 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h18 := h7 h17
        -- One of the premise coincides with the conclusion.
        exact h18
      case inr h19 =>
        -- Conjunctions on the left can always be decomposed.
        let h20 := h19.left
        let h21 := h19.right
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h22 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h23 := h7 h22
        -- One of the premise coincides with the conclusion.
        exact h23
    case inr h24 =>
      -- Conjunctions on the left can always be decomposed.
      let h25 := h24.left
      let h26 := h24.right
      -- One of the premise coincides with the conclusion.
      exact h26
  case inr h27 =>
    -- Conjunctions on the left can always be decomposed.
    let h28 := h9.left
    let h29 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h28
    case inl h30 =>
      -- Disjunctions on the left can always be decomposed.
      cases h30
      case inl h31 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h32 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h33 := h7 h32
        -- One of the premise coincides with the conclusion.
        exact h33
      case inr h34 =>
        -- Conjunctions on the left can always be decomposed.
        let h35 := h34.left
        let h36 := h34.right
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h37 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h38 := h7 h37
        -- One of the premise coincides with the conclusion.
        exact h38
    case inr h39 =>
      -- Conjunctions on the left can always be decomposed.
      let h40 := h39.left
      let h41 := h39.right
      -- One of the premise coincides with the conclusion.
      exact h41



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316914774701424105845784038999 : (p3 ∨ (p2 → (((p2 → p1) ∨ ((p4 ∨ p5) ∧ ((p1 ∨ p3) ∧ (p1 → (p5 ∨ (p2 ∨ ((p5 ∧ p2) ∧ ((True → True) ∨ p1)))))))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64796364022064213809216585541 : ((p2 ∨ (((True → p1) ∧ ((True ∧ ((p5 → (p1 → p2)) → ((True ∨ p5) ∨ p5))) → (((p2 ∧ (p5 ∧ p1)) ∨ p4) → False))) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300141635374383220732090327462 : (False ∨ ((p3 ∧ (((False ∨ p5) ∧ (False ∨ p2)) ∨ ((p4 ∧ (p3 ∨ (((((p3 → True) ∧ False) ∨ p5) ∨ p2) ∨ p2))) ∨ p5))) ∨ (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50007829534394505481420132147 : (((((True ∨ (((False ∨ p2) ∨ True) ∨ p3)) → p5) → ((p3 ∧ ((p4 ∧ (False ∨ p4)) ∨ p5)) → p1)) ∧ (((p2 ∧ p1) → p2) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49434786063514169805272114329 : (((((p5 → (((p5 ∨ ((p4 → (False ∧ (p5 → p4))) ∧ (p5 ∨ (p4 → p3)))) → p3) ∨ True)) → p4) ∨ p2) → (p3 ∧ (p5 ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134866032628957389344809505664 : (((False → (p2 ∧ ((p2 → p5) ∧ ((p5 ∧ p1) → ((True ∨ p4) ∨ (True ∨ (((p1 ∨ True) → False) ∧ p1))))))) → False) ∨ ((True ∧ True) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60255647413053368496035950715 : (((False → p1) → ((((p1 → ((p5 ∧ (False ∧ ((True → True) ∧ p2))) ∨ ((p5 → True) → (p5 ∧ (p4 ∧ p5))))) ∨ p2) ∨ p4) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54121115733199425918627634532 : (((True ∨ ((False → p2) ∧ (p2 → (p1 ∨ (False ∨ False))))) → (((p2 ∨ (p2 ∨ True)) ∨ False) ∨ (True → ((p2 → p2) → (p1 → p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147826064224166717799407486981 : (((False ∨ (((False → (p1 ∨ (True → ((p5 ∨ False) → p5)))) → p1) ∧ (p3 → ((p3 ∨ True) → p1)))) → p5) ∨ (p4 → (True ∨ (p3 ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308378781986630566289356768409 : (p2 ∨ ((((((p2 → ((True ∧ p4) ∧ (p3 ∨ p5))) → (p5 → (True → (p1 ∨ ((True ∧ False) ∨ p2))))) ∨ p3) ∨ (p4 → p5)) ∨ True) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324589049124055541285388531691 : (p5 ∨ (((False ∧ p1) → True) ∧ (((((True → p3) → (False ∨ p4)) ∨ (False ∨ True)) ∨ p4) ∨ (p1 ∨ (True → (p3 → ((False → p1) → p3))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_807638522398735129018488222182 : (((p4 → ((p1 ∧ ((p5 ∨ p4) ∨ True)) → ((((p1 → (p3 ∧ p4)) ∨ ((p2 ∨ False) ∨ (p2 ∧ (p3 ∨ False)))) ∧ True) ∧ (p4 ∨ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684433102440891581081690801632 : (((((((True → ((p4 ∨ p3) → p4)) → p5) → p3) ∨ (p4 → (((p1 ∧ False) ∧ p2) ∨ True))) ∨ (((False ∧ p5) ∨ p1) → (p4 → p1))) ∨ p5) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136074485917252670341181895703 : ((((p3 → p4) → (p1 ∧ ((p2 ∧ p1) ∧ p2))) ∧ (True → (p5 → ((((p1 → p5) → p5) → (p1 ∧ True)) ∨ True)))) ∨ ((False ∧ p5) → p1)) := by
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
theorem thm_5_vars_217512412273237726889889592969 : ((((p4 ∨ p5) ∧ True) → p2) → (((True → p5) ∨ (False ∨ (p4 ∧ ((p5 ∨ (p1 → True)) ∨ ((False → p3) ∨ p4))))) ∨ (False → (p1 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118728173410492198723596368000 : ((p5 ∨ ((((p2 ∨ (p1 ∨ True)) ∨ p1) → (((((p5 ∧ p5) → p1) → False) → True) → p2)) ∨ ((p3 ∧ (p1 ∨ False)) → True))) ∨ (False ∨ p1)) := by
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
theorem thm_5_vars_54650371145686368715293330413 : (((((((p4 → p1) ∧ p1) → p5) → p3) ∨ p1) → (p5 ∨ ((((False ∧ (p1 ∧ ((False ∨ (p1 ∧ p4)) ∧ p4))) ∧ p4) ∨ False) ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113053627178460736524616185793 : (((p1 ∨ (False → (False ∧ ((False → p1) → ((((False ∨ True) ∧ (p5 ∨ p4)) → (False → (p3 → p3))) ∨ (True ∧ p1)))))) → p5) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698413297430481730600348834394 : (((((p4 → (p1 ∧ (True → (True ∨ (p3 ∧ p1))))) → (p5 ∧ p4)) ∨ (False → (((p2 → p3) → p5) ∨ (p2 ∨ ((p3 ∨ p5) ∧ False))))) ∨ False) ∧ True) := by
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
theorem thm_5_vars_345726164399681174865871767001 : (p3 → ((p4 → (((((False → p4) ∨ ((((p4 → False) ∨ True) ∨ True) ∨ (False ∨ (p5 ∧ True)))) ∧ p5) ∧ (p1 ∨ (p4 ∨ True))) ∨ p2)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64404890317037659810259930546 : ((p1 ∨ ((((p3 ∨ (True → (True ∧ (p4 ∨ False)))) ∨ p4) ∧ ((p2 ∨ ((False ∧ p3) → False)) ∧ ((p2 ∨ (True ∨ p2)) → p2))) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41552573590113652015768141844 : (((((((p4 ∨ p2) ∧ p2) ∧ ((p2 ∧ p2) ∨ p2)) ∧ p5) → (p5 → (p3 → (True ∧ ((((p2 → True) ∧ p1) ∨ p4) ∨ True))))) ∨ p3) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
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
    cases h7
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
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
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h19 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187061654256139215244989017391 : (((p1 ∨ True) ∧ ((((False → p4) → False) ∨ p3) → (True → p2))) → ((True → (((p5 ∧ (p2 ∨ p3)) → p5) → p5)) → ((p5 → p5) ∧ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h11 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h12 := h2 h11
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h13 : ((p5 ∧ (p2 ∨ p3)) → p5) := by
      -- Implications on the right can always be decomposed.
      intro h14
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h18 =>
        -- One of the premise coincides with the conclusion.
        exact h15
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h19 := h12 h13
    -- One of the premise coincides with the conclusion.
    exact h19
  case inr h20 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h21 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h22 := h2 h21
    -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
    have h23 : ((p5 ∧ (p2 ∨ p3)) → p5) := by
      -- Implications on the right can always be decomposed.
      intro h24
      -- Conjunctions on the left can always be decomposed.
      let h25 := h24.left
      let h26 := h24.right
      -- Disjunctions on the left can always be decomposed.
      cases h26
      case inl h27 =>
        -- One of the premise coincides with the conclusion.
        exact h25
      case inr h28 =>
        -- One of the premise coincides with the conclusion.
        exact h25
    -- We have shown the premise of h22, we can now drive its conclusion.
    let h29 := h22 h23
    -- One of the premise coincides with the conclusion.
    exact h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192751860907581853298076748844 : ((((p1 → p2) → ((False ∧ (p4 ∧ p4)) ∧ p5)) → p1) → ((p4 ∧ p3) → ((p2 → p4) ∨ ((True → (((p3 ∧ p5) → p2) ∧ p5)) ∧ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h5
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_710283376502328918515960824391 : (((((p4 ∨ (p1 ∨ (False ∧ p2))) ∨ p4) ∧ ((p4 → ((False ∨ ((p1 → (p5 → False)) ∧ (p2 ∨ (True ∧ p4)))) ∨ p1)) → (False ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113690429732533457384009217621 : (((((False ∧ (((((True ∧ (p1 → p2)) ∧ (p4 → p4)) ∨ False) ∨ p2) → p1)) ∧ ((p1 → p4) ∨ p1)) → p3) → (p4 ∨ p1)) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_458688213214373911743832384429 : ((((True → (((p5 ∨ ((False ∧ p1) → ((p5 → (p4 ∧ True)) ∨ p3))) ∧ p1) ∨ (p4 ∧ p2))) ∨ (((False → (p2 ∨ False)) → p3) ∨ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37070277324964272362117880162 : (((((p2 → ((True ∧ ((False ∨ (((((p1 ∨ True) ∨ p2) ∧ (p5 ∨ (False ∨ False))) ∧ False) ∧ p5)) ∨ p5)) ∧ p5)) ∧ p3) ∧ True) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_692706393983680954609316624627 : (((((((p5 ∨ (p1 ∧ p5)) ∨ p3) → p3) → (p3 → (p1 ∧ (p2 → p2)))) ∧ (p2 ∨ (False → ((((p4 ∨ p3) ∨ p3) ∧ True) → p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325698761631319944195936109044 : (p5 ∨ (p1 ∨ ((((p2 ∧ False) ∨ p5) ∨ (p2 → p2)) ∧ ((True ∨ (((p4 ∧ (False ∧ p3)) ∨ (p2 ∨ p4)) ∨ (p2 → (True ∧ p3)))) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125016278283262550716132722848 : ((((p2 ∨ p1) ∨ True) ∧ ((p1 → p1) → ((p5 ∧ ((True → False) ∨ False)) ∧ ((False ∧ (p4 ∧ ((p2 → p5) ∧ False))) ∨ False)))) → (False ∧ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h6 : (p1 → p1) := by
        -- Implications on the right can always be decomposed.
        intro h7
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h8 := h3 h6
      -- We need to get the right conjuct of h8 based on <expert-advice>.
      let h9 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- False on the left can always be used.
        apply False.elim h11
      case inr h13 =>
        -- False on the left can always be used.
        apply False.elim h13
    case inr h14 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h15 : (p1 → p1) := by
        -- Implications on the right can always be decomposed.
        intro h16
        -- One of the premise coincides with the conclusion.
        exact h16
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h17 := h3 h15
      -- We need to get the right conjuct of h17 based on <expert-advice>.
      let h18 := h17.right
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- Conjunctions on the left can always be decomposed.
        let h20 := h19.left
        let h21 := h19.right
        -- False on the left can always be used.
        apply False.elim h20
      case inr h22 =>
        -- False on the left can always be used.
        apply False.elim h22
  case inr h23 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h24 : (p1 → p1) := by
      -- Implications on the right can always be decomposed.
      intro h25
      -- One of the premise coincides with the conclusion.
      exact h25
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h26 := h3 h24
    -- We need to get the right conjuct of h26 based on <expert-advice>.
    let h27 := h26.right
    -- Disjunctions on the left can always be decomposed.
    cases h27
    case inl h28 =>
      -- Conjunctions on the left can always be decomposed.
      let h29 := h28.left
      let h30 := h28.right
      -- False on the left can always be used.
      apply False.elim h29
    case inr h31 =>
      -- False on the left can always be used.
      apply False.elim h31
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
      have h36 : (p1 → p1) := by
        -- Implications on the right can always be decomposed.
        intro h37
        -- One of the premise coincides with the conclusion.
        exact h37
      -- We have shown the premise of h33, we can now drive its conclusion.
      let h38 := h33 h36
      -- We need to get the left conjuct of h38 based on <expert-advice>.
      let h39 := h38.left
      -- We need to get the left conjuct of h39 based on <expert-advice>.
      let h40 := h39.left
      -- One of the premise coincides with the conclusion.
      exact h40
    case inr h41 =>
      -- We want to use the implication h33 based on <expert-advice>. So we show its premise.
      have h42 : (p1 → p1) := by
        -- Implications on the right can always be decomposed.
        intro h43
        -- One of the premise coincides with the conclusion.
        exact h43
      -- We have shown the premise of h33, we can now drive its conclusion.
      let h44 := h33 h42
      -- We need to get the left conjuct of h44 based on <expert-advice>.
      let h45 := h44.left
      -- We need to get the left conjuct of h45 based on <expert-advice>.
      let h46 := h45.left
      -- One of the premise coincides with the conclusion.
      exact h46
  case inr h47 =>
    -- We want to use the implication h33 based on <expert-advice>. So we show its premise.
    have h48 : (p1 → p1) := by
      -- Implications on the right can always be decomposed.
      intro h49
      -- One of the premise coincides with the conclusion.
      exact h49
    -- We have shown the premise of h33, we can now drive its conclusion.
    let h50 := h33 h48
    -- We need to get the left conjuct of h50 based on <expert-advice>.
    let h51 := h50.left
    -- We need to get the left conjuct of h51 based on <expert-advice>.
    let h52 := h51.left
    -- One of the premise coincides with the conclusion.
    exact h52



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110711677261307978314555421018 : ((((((p3 ∨ ((False ∨ p2) ∨ ((True → ((False → p1) ∨ p4)) ∧ ((p5 → (True → False)) → True)))) ∨ p1) → p3) ∧ True) ∧ p4) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329288663348390664292751919080 : (True → ((True ∧ (False ∧ p1)) ∨ (((p2 → (False ∧ (p4 → (((p3 → ((p4 ∨ p5) ∧ p1)) ∨ (p1 → p1)) ∨ p2)))) ∨ (p3 → False)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58969777916267317208812395609 : (((p2 ∧ p3) ∨ (((p2 → (p2 → ((p1 ∧ (p5 ∨ (((True → p1) ∨ False) ∨ p4))) ∨ True))) ∨ p3) → ((True ∨ p3) → (p1 ∧ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123667753781188191241206321666 : ((((p3 ∧ (p3 → p1)) → ((((True → p1) → p2) ∧ (p2 ∧ (p4 → p5))) → p5)) → ((((p4 ∧ False) ∧ False) ∨ p5) ∨ p1)) → (p2 → p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_633593875952074533756328562109 : (((((((p3 ∨ p2) → p1) ∧ (((p4 → (True ∧ p4)) → p2) ∧ (((((p3 ∨ p3) → p5) → p2) ∧ p1) ∨ False))) ∨ (False ∨ True)) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190625641473674163333985677343 : (((p2 ∧ (False → ((p3 ∨ p4) → (p5 ∨ True)))) → p5) ∨ (p1 → ((True ∨ (True → (p5 → False))) ∨ (((p3 → (True ∧ p1)) ∧ p5) ∨ p3)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213509522221985149014305824312 : (((p4 → (False ∧ p5)) ∧ p4) ∨ (((((False ∨ ((((False ∧ (False → p1)) ∨ p4) → (p3 → False)) ∨ p2)) → p4) ∨ p4) ∨ p2) → (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h5 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304900423449192047802883251554 : (p1 ∨ ((False → (p4 ∧ (((False → ((p1 ∧ p4) ∧ False)) ∧ (((p3 → (p2 ∧ False)) ∨ True) ∨ ((False ∨ False) ∧ p5))) ∧ True))) → (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140910514610541638109162786050 : ((((p2 → (p5 ∧ (p4 ∧ p2))) → ((p3 ∨ p3) → p3)) ∧ (p4 → (((p1 ∨ (p4 → p2)) → (p4 ∨ False)) ∨ p4))) → ((True → p4) ∨ True)) := by
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
theorem thm_5_vars_46771535682251463439615381136 : (((p3 → ((((((p4 → p4) → p2) → (p2 → p2)) → (p3 ∨ True)) ∨ (p1 → p2)) → (p2 ∧ (p1 ∧ (True ∨ p5))))) ∧ (p4 ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_212273682666840316375788713957 : ((False ∨ (p5 → (False → p1))) ∧ (True ∧ (p1 ∨ (((p3 → (False ∨ False)) ∧ (p4 ∧ (p5 ∨ False))) ∨ (((p1 → p4) → (False → False)) ∨ p2))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111518483639982533818765701712 : (((p5 → ((p2 ∧ True) ∧ ((((True ∧ (((p3 ∧ p4) ∨ False) → p1)) ∨ ((False ∨ p1) ∧ p4)) ∨ p2) → (p4 ∧ p3)))) ∧ True) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340147332000775917850092610517 : (p1 → (p4 → ((p2 → (((p3 ∨ ((p3 ∧ False) ∧ (p3 ∧ False))) ∧ (p1 ∧ p5)) ∨ (((p5 ∨ False) → ((False → p3) → p5)) ∨ False))) ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149602416692945307079429594683 : ((p3 ∧ ((((p4 → p2) → (p4 ∧ p4)) ∧ p1) ∧ ((((p4 ∧ True) ∧ p1) ∨ (p4 → p2)) ∧ (p5 ∨ True)))) ∨ (p1 → ((True ∧ True) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192846872630558458742067187798 : ((((p1 → (p5 ∨ (p3 → p1))) ∨ False) ∧ (p4 ∧ p2)) → ((((p4 ∧ ((p2 ∧ True) → p5)) ∨ (p5 ∨ True)) ∨ p4) → ((p5 → False) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h7 := h1.left
      let h8 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h8.left
        let h11 := h8.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h12 =>
        -- False on the left can always be used.
        apply False.elim h12
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h1.left
        let h16 := h1.right
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h17 =>
          -- Conjunctions on the left can always be decomposed.
          let h18 := h16.left
          let h19 := h16.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h19
        case inr h20 =>
          -- False on the left can always be used.
          apply False.elim h20
      case inr h21 =>
        -- Conjunctions on the left can always be decomposed.
        let h22 := h1.left
        let h23 := h1.right
        -- Disjunctions on the left can always be decomposed.
        cases h22
        case inl h24 =>
          -- Conjunctions on the left can always be decomposed.
          let h25 := h23.left
          let h26 := h23.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h26
        case inr h27 =>
          -- False on the left can always be used.
          apply False.elim h27
  case inr h28 =>
    -- Conjunctions on the left can always be decomposed.
    let h29 := h1.left
    let h30 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h29
    case inl h31 =>
      -- Conjunctions on the left can always be decomposed.
      let h32 := h30.left
      let h33 := h30.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h33
    case inr h34 =>
      -- False on the left can always be used.
      apply False.elim h34



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47026502826173103222036009869 : ((((p1 → (((((((True ∨ p3) ∧ p4) ∧ p2) → p3) ∧ True) ∨ (False ∧ False)) → (p1 ∨ (True ∧ (False → p5))))) → p2) ∨ (True ∧ True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260197549051060182900393569394 : ((p2 → p2) → (True ∧ (((((((((p3 ∧ False) ∨ False) ∨ p2) → p4) ∨ (p5 ∨ p1)) → p2) ∧ (p5 ∧ p5)) ∨ False) ∨ (p3 ∨ (p5 → p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57708761155269748593289155082 : ((((p3 ∧ p3) → p3) → (p1 → ((False ∧ ((p2 ∧ (p2 → ((True ∧ (True → p2)) → (True ∨ True)))) ∨ p5)) ∧ (False → (p1 ∨ True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60032214486544932628030947073 : (((p1 ∨ p3) → (((p2 ∧ p1) ∨ (((((((True → p1) ∧ p1) → p4) → p1) ∧ (p3 → p4)) ∨ False) ∨ p3)) ∧ ((True ∧ False) ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48617372521320866721954207096 : (((((p1 ∨ p1) → (((p3 → (p3 ∨ p3)) ∨ ((False ∨ (True ∨ False)) → (p4 ∨ True))) → p5)) → (p5 → p2)) ∧ (True ∧ (p1 ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_791464344545415642169366162774 : (((True → ((False ∧ (p2 ∧ (((p2 ∨ (((False ∨ p4) ∨ (False ∨ p2)) → p5)) ∧ (True ∧ ((p3 ∧ (p2 → p2)) ∨ p5))) ∧ False))) ∨ True)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_338020707338744063791678387766 : (p1 → ((p1 ∨ (p1 ∨ (((p3 ∧ p4) ∧ (p3 ∧ p4)) → p5))) ∧ (((p3 ∧ (p4 ∨ (p3 ∧ ((p5 ∨ False) ∨ p3)))) ∧ p3) ∨ (p1 ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657007396810231971712885563082 : (((((p5 → ((True ∨ p3) ∧ False)) → ((((False ∧ p2) ∨ p5) ∧ (((False → (True ∧ p3)) → p2) ∨ p1)) → (p3 ∧ True))) ∨ (False → False)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_621312172694668822550551121040 : ((((True ∧ (((p1 ∨ (p4 → (p3 ∨ p4))) ∧ True) → (((p3 ∨ ((p5 → p1) ∧ p3)) ∧ (((True ∧ p1) ∨ p2) → False)) ∨ True))) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_179368739689926083936863067577 : ((p2 ∨ ((p2 → p2) ∧ (((p2 ∨ p5) ∨ (p3 ∨ p4)) ∨ (p5 ∧ p2)))) ∨ (((False ∧ p4) ∧ ((p3 ∧ (p1 ∧ p4)) ∨ p5)) → (p4 ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662872489003174273601148269094 : (((((p1 → (p1 ∨ p2)) ∧ (p4 ∧ (((p2 → False) ∨ (p2 ∨ (p4 ∨ p3))) ∧ (p4 → ((p1 → (True → p3)) ∧ False))))) → (p4 → False)) ∨ p2) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h10 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h11 := h8 h10
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h15 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h16 := h8 h15
      -- We need to get the right conjuct of h16 based on <expert-advice>.
      let h17 := h16.right
      -- False on the left can always be used.
      apply False.elim h17
    case inr h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h20 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h19
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h21 := h8 h20
        -- We need to get the right conjuct of h21 based on <expert-advice>.
        let h22 := h21.right
        -- False on the left can always be used.
        apply False.elim h22
      case inr h23 =>
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h24 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h5
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h25 := h8 h24
        -- We need to get the right conjuct of h25 based on <expert-advice>.
        let h26 := h25.right
        -- False on the left can always be used.
        apply False.elim h26
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303045751684418445377559416265 : (False ∨ (p2 → (((p5 ∨ False) → ((((((True ∧ ((p3 ∨ p3) ∨ p5)) ∧ ((p5 ∧ p1) → p3)) ∨ p3) → False) ∨ p5) ∧ (True ∨ p3))) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116378732045679991116481430885 : ((((p1 → p1) → p1) → (p5 → (True → ((p2 → ((p4 ∨ (p1 ∨ False)) ∧ (p2 → p3))) ∨ ((p5 ∨ (p1 ∧ p4)) ∧ p3))))) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_758464860973369872860193386766 : (((p2 ∧ ((p3 ∧ ((p3 ∧ (((p3 ∨ (p1 → (True ∨ (True ∧ p3)))) ∨ ((p4 ∨ p1) → (True ∨ False))) ∧ p3)) ∧ (p5 ∧ p1))) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158959790473620166558990874264 : ((p2 ∨ (p3 ∨ ((((((p1 ∨ p5) ∨ (p1 ∨ (p2 ∧ p4))) ∧ p5) ∧ (False ∧ p1)) ∨ False) ∨ True))) ∨ (p3 ∨ (((p5 → True) → p1) ∧ p5))) := by
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
theorem thm_5_vars_42670466104180557884679022825 : (((p4 ∨ ((p5 → p4) ∨ (((p4 → p3) ∧ (p3 ∧ ((p1 ∨ p4) ∨ p3))) → ((p1 ∧ ((False → (True → p1)) ∧ p5)) ∨ True)))) ∨ p2) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  let h4 := h3.left
  let h5 := h3.right
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157147780098691589871132546964 : ((((((((True → p1) → p1) ∨ p1) ∨ ((p4 ∨ (p3 ∧ False)) ∨ p5)) ∧ (p5 ∨ p3)) ∨ p4) → p3) ∨ (((p3 ∨ True) ∨ p5) ∨ (p1 → p4))) := by
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
theorem thm_5_vars_244756348531154616539631859647 : ((p1 ∧ False) ∨ (((True → ((p1 ∨ ((p1 ∨ p4) → p1)) → (p2 ∨ (True → p1)))) → p5) ∨ (False ∨ (False → (p1 ∧ ((p4 → True) ∧ False)))))) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117085286373165639906481696734 : (((False → p4) → (((((p1 → False) → p3) → (p2 ∨ p4)) ∨ ((((True ∧ p2) → (p5 ∨ p1)) → (p1 ∨ p4)) ∨ True)) ∨ p1)) ∨ (p2 ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_169852476561787376944529831582 : (((((((p2 ∨ True) ∨ p2) ∧ False) ∨ (p3 ∨ (p5 → p5))) ∨ False) ∨ (True ∧ p4)) ∧ ((False ∨ True) → (((p5 ∨ (p1 ∧ p3)) ∨ True) ∨ False))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_155478977716371542180207545556 : (((p2 ∨ (True ∨ p5)) ∧ (((p3 ∨ p1) ∨ (p1 → (True ∧ ((p3 → (False ∨ False)) ∨ p1)))) ∨ p4)) ∧ (p1 ∨ (p4 → ((True ∨ p3) ∨ p4)))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161432964487801856446096744171 : ((p2 ∧ ((p1 ∨ (((p1 → True) ∧ p3) → p2)) → (((p5 ∧ (p1 → False)) ∨ (p2 ∨ p4)) ∧ False))) → ((((p3 ∨ False) → p1) → p2) ∧ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : (p1 ∨ (((p1 → True) ∧ p3) → p2)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h11 := h6 h7
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180149350846695817467861759779 : (((((p5 → True) → (p1 → (p2 ∧ (False ∧ p3)))) ∧ (p5 ∨ True)) → p5) → ((False ∨ p1) ∨ (((True ∧ False) ∨ ((p4 ∧ True) ∨ p4)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_724745032466953604744132267164 : ((((p3 ∨ (False ∨ p4)) ∧ ((p1 ∨ (p3 ∨ ((p3 ∨ True) ∧ (((p3 → False) ∨ p1) → (True ∨ (p4 ∨ p5)))))) ∨ ((True → False) → True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_595005443861688016504042954965 : ((((((((((p1 ∧ p5) ∨ p1) ∧ p3) → True) → (p1 → p4)) → (False ∧ False)) ∨ (p3 → (p2 ∧ (((p5 ∧ True) → p1) ∨ p1)))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208536523869101624040952883581 : (((False ∨ p2) → ((p5 ∧ p5) ∧ p3)) → (((((p3 ∨ p5) ∧ p2) → ((p5 ∧ p3) ∧ p2)) ∨ ((p3 ∨ True) → p2)) ∨ ((p3 → p1) ∧ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h6 : (False ∨ p2) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h7 := h1 h6
    -- We need to get the left conjuct of h7 based on <expert-advice>.
    let h8 := h7.left
    -- We need to get the left conjuct of h8 based on <expert-advice>.
    let h9 := h8.left
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- One of the premise coincides with the conclusion.
    exact h10
  -- Conjunctions on the left can always be decomposed.
  let h11 := h2.left
  let h12 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h13 =>
    -- One of the premise coincides with the conclusion.
    exact h13
  case inr h14 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h15 : (False ∨ p2) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h12
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h16 := h1 h15
    -- We need to get the right conjuct of h16 based on <expert-advice>.
    let h17 := h16.right
    -- One of the premise coincides with the conclusion.
    exact h17
  -- Conjunctions on the left can always be decomposed.
  let h18 := h2.left
  let h19 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h18
  case inl h20 =>
    -- One of the premise coincides with the conclusion.
    exact h19
  case inr h21 =>
    -- One of the premise coincides with the conclusion.
    exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48925564604083427109916091386 : (((((((p3 → ((False → p2) ∧ False)) ∨ ((p5 → p1) → ((p1 ∨ p1) ∨ p4))) ∨ (p3 ∧ p5)) → p4) ∧ p1) ∨ (True ∨ (p4 ∧ p2))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157780070522845755548703191565 : ((((p3 ∧ ((p1 ∨ (p4 → (p1 → (p2 ∨ p2)))) → p4)) → p4) ∨ (False ∧ (p2 ∨ (p4 ∧ False)))) ∨ ((False ∧ p4) → ((p4 ∨ True) ∧ p1))) := by
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
  apply False.elim h2
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_144593498312102249304941026383 : (((p3 → ((((p5 ∧ p4) ∨ p5) ∧ (p4 → (((False ∨ (p3 → p4)) ∨ p2) ∨ p5))) ∨ p1)) ∨ (p5 → p5)) ∧ (((False ∧ p4) → p3) ∨ p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356778127852888080764742288405 : (p5 → ((p5 ∧ ((p5 → (p2 ∧ p4)) ∨ True)) → (((p1 ∧ True) ∨ p2) ∨ (False ∨ (((False ∨ (p3 ∧ (p5 ∨ (p1 → False)))) ∨ True) ∧ True))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166574387172243787516588132909 : ((True → ((p4 → (p4 ∧ (p3 ∧ (p1 ∨ ((False ∨ (p1 ∧ (p1 → False))) ∨ p1))))) ∨ p4)) ∨ (True ∨ ((p2 ∧ ((p2 ∧ True) ∨ p4)) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51318370785597486882616598707 : (((p5 ∨ ((False ∨ (((p4 ∨ p5) ∧ True) ∧ (p5 → (p1 ∧ (p3 → p1))))) ∧ (True ∧ p3))) ∨ ((True ∨ ((p1 → p2) ∨ p5)) ∨ p3)) ∨ False) := by
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
theorem thm_5_vars_199875036109330028712045565074 : (((p4 → ((True ∧ True) → p3)) ∧ (False → True)) → (((p4 → ((True → p2) ∨ False)) ∨ (True ∨ p3)) ∧ (False → (p2 ∧ (p3 → (p4 ∧ p2)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_814337048175018583892139659896 : ((((((((p3 → p1) ∧ (((((False → p1) ∨ True) ∨ False) → p3) → ((p4 ∨ p2) → (p2 → p5)))) ∧ p3) ∨ (p1 ∧ p3)) ∨ False) ∧ True) → p1) ∧ True) := by
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
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h10 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h11 := h8 h10
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- One of the premise coincides with the conclusion.
      exact h13
  case inr h15 =>
    -- False on the left can always be used.
    apply False.elim h15
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704001653735863218252172605222 : ((((((p5 ∨ ((True ∨ (p2 ∧ p4)) ∨ p5)) → p3) → p4) → ((p2 ∨ (((True ∨ True) ∨ False) ∧ (p5 → (p4 ∨ p3)))) ∧ (p1 ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_675899368235281076011569711764 : (((((((False ∨ ((False → p1) → (p5 ∧ p4))) → p4) → p1) ∧ (p2 → (((p3 ∨ p4) ∧ p4) ∨ p3))) ∧ (p5 → (p2 ∨ (p1 ∨ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308725131912822045906973381037 : (p2 ∨ ((p1 → ((p3 ∧ ((p2 ∨ ((p2 ∧ ((p2 ∨ False) ∨ (True ∨ (((p4 → (True → True)) → p3) ∧ False)))) ∨ p4)) ∨ p3)) ∨ p1)) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_587571067496215658923141018721 : ((((((p4 → (True → (p4 ∧ (p3 ∧ (p3 → (((p3 ∧ p3) → (p4 ∧ (p2 ∧ p1))) ∨ (True ∧ (p5 ∨ False)))))))) ∨ p5) ∨ False) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326797847344686256085022744282 : (True → ((p2 → ((p4 ∧ (p2 ∧ ((((((True ∧ (p4 ∧ p1)) → ((p3 ∨ p5) ∧ p1)) ∨ False) ∨ (p3 ∨ False)) → p3) ∧ False))) ∨ p2)) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50255190908011260055386122624 : ((((p3 ∧ (p4 ∧ (((True → p3) ∨ p1) ∧ (((False ∧ ((p3 ∧ p3) ∧ p3)) ∨ True) → p1)))) → False) ∨ ((p2 ∧ (p3 ∧ p5)) → p2)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314640558860437054065650519716 : (p3 ∨ (((p2 ∨ ((p5 → (p4 ∨ ((p2 ∧ p1) → (True ∧ (p4 ∧ True))))) → p2)) ∧ False) ∨ (True ∨ (p2 ∧ ((p2 ∧ True) ∧ (p5 ∨ p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324533894225652325743670113441 : (p5 ∨ ((((p1 → True) ∨ True) → p1) → (((p4 ∨ (False ∨ False)) ∧ (((True ∧ p1) → p4) ∨ (p3 ∨ (p3 ∧ ((False → False) → False))))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259293949742849099055830299018 : ((False → p1) → (p1 ∨ ((((p1 ∨ ((p5 → p3) ∨ True)) ∧ p1) ∨ True) ∨ ((p4 ∨ p1) ∨ (p5 ∨ ((p4 → p5) → ((p5 ∨ p2) ∨ p4))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_932669914451962675110812195212 : (((((p3 ∨ True) → ((p1 ∨ (True ∧ True)) ∧ p3)) ∧ (False → (p1 ∨ (True ∧ (((p3 ∨ p1) → ((p5 ∨ p3) ∧ (p2 ∧ p5))) ∨ p4))))) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p3 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
theorem thm_5_vars_66206222957152152502323238434 : ((p5 ∨ ((p1 ∨ ((True ∧ (((p4 ∧ p4) ∨ (True ∧ False)) ∧ (p3 ∨ p4))) ∨ p5)) ∨ (True ∨ ((((p2 ∧ p3) → p2) → p5) ∨ False)))) ∨ p2) := by
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
theorem thm_5_vars_892362870686547335462294896051 : (((((((p1 ∨ ((((p2 → p5) ∧ (True ∨ ((p5 → True) ∧ p5))) ∨ p2) ∨ p4)) ∨ p1) ∧ (True → p4)) → True) ∧ ((p5 ∨ True) → False)) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p5 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690723806379727999893868323729 : ((((((p3 ∨ (p5 → ((((True ∧ p2) ∨ True) ∧ p3) ∨ (False → p4)))) ∧ p2) → p5) → (((p4 → (p1 → p5)) → False) ∨ (p4 ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_652226145244128417385049442900 : ((((p2 ∧ ((p1 → p5) ∨ (((p4 ∨ (p3 ∨ ((p2 → (p5 ∧ ((True → p2) ∧ p5))) → p2))) ∨ (p5 ∧ p5)) ∧ p5))) ∧ (p2 ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327049814701352431600801398173 : (True → (((True ∨ ((p3 ∨ (p1 → p4)) ∨ (p1 → True))) → ((p3 → ((((p5 ∧ (p5 ∧ p1)) → p2) ∨ (False → p2)) ∧ p2)) ∧ p3)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65225256327476755233213338702 : ((p3 ∨ ((p1 ∧ (((p2 → p4) → p5) → ((False → ((True → ((p4 ∧ False) → p1)) → p2)) ∧ (p5 → (p2 ∧ (True ∧ p4)))))) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



