variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42164707995367017641150912006 : ((((p4 → p1) → ((p4 ∧ (((False ∧ (False ∧ (False ∧ ((p2 → p5) → p5)))) ∧ p4) → ((p1 ∧ p3) → p3))) ∨ (False ∨ p1))) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69251331635973406722838091962 : ((p5 → (((False ∨ p2) ∨ p2) → (((True → (True → (p1 → (((False → (True ∨ False)) ∨ p3) → (p1 ∧ (False ∨ p2)))))) → p3) ∨ True))) ∨ p2) := by
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
    cases h3
    case inl h4 =>
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190133076200754885785617010686 : ((((p5 ∧ p5) ∧ (True → ((p5 ∨ p1) → False))) ∧ p1) ∨ ((False → (((p3 ∧ p5) → ((p4 ∨ True) ∧ True)) ∨ (True → False))) ∨ (True ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221882356507925963566049293071 : (((p4 ∧ p2) → p4) ∧ (((((False ∨ (p3 → p4)) ∧ p3) ∧ (p2 ∧ False)) ∨ True) ∨ ((p5 → ((p1 ∨ p4) ∧ p2)) ∧ ((p1 ∨ p1) → p5)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158111196115310698058049689330 : ((((p5 ∧ p5) → (p5 ∨ True)) ∧ (p5 ∧ ((p4 ∧ p2) ∨ (((p2 → (p1 → p5)) ∧ False) ∧ p3)))) ∨ (False → ((p5 ∧ (p4 → p1)) ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257021718104319648478287997197 : ((p2 ∨ True) → ((((True → ((p3 ∧ (False ∨ (p3 ∧ p1))) ∨ (p5 ∧ (False ∨ p4)))) ∧ False) → True) ∧ ((p5 ∨ p5) ∨ (p4 ∨ (p2 → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41801407650023623620967412944 : ((((False ∨ (p3 → (p3 ∧ False))) → ((True → ((p2 → (p1 ∧ (p2 → (((False ∧ (False ∧ True)) ∨ p3) ∧ p5)))) ∨ p1)) ∨ False)) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178656325511278626018635305977 : ((((p3 ∨ (False ∧ p3)) ∨ p4) ∧ (False → (((True → p2) ∨ True) ∧ p3))) ∨ (p3 ∨ (p3 ∨ (p5 → (p1 ∨ (p1 ∨ (p5 ∨ (p1 ∨ p4)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231170496333233153093094781494 : (((p2 ∨ p2) ∨ p2) → (p1 → ((p3 → (((p4 ∨ (True ∧ (True → (((p2 → False) ∨ p3) ∧ p1)))) ∧ (p2 ∧ p4)) ∧ p4)) ∨ (p1 ∨ p4)))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186158575950055608747141536101 : ((((p4 ∨ p5) ∨ ((p5 → p3) ∨ ((False ∧ p5) ∨ p5))) ∨ True) → (((p1 ∨ ((p3 → p4) ∧ p2)) ∨ (True ∨ (p2 ∨ (False ∨ p3)))) ∨ p5)) := by
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
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Conjunctions on the left can always be decomposed.
          let h10 := h9.left
          let h11 := h9.right
          -- False on the left can always be used.
          apply False.elim h10
        case inr h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h12
  case inr h13 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260608550042165487507233439602 : ((p3 → p2) → (((p1 ∧ ((p2 ∧ (((False ∨ p5) → p4) ∧ p5)) → p2)) → p1) → (p2 → ((p2 ∨ p2) ∨ (p5 ∨ ((p5 ∨ False) → p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305182760467963539127387463116 : (p1 ∨ ((((p2 ∧ False) → p4) → (((p3 → False) ∨ (True ∨ (True ∨ p5))) ∧ (((False ∨ False) → p2) → p3))) ∨ ((True ∨ (p5 → True)) ∨ p3))) := by
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
theorem thm_5_vars_226499743767056727012015285472 : (((p2 → p4) ∨ p5) ∨ (((p4 ∨ p5) → ((((p3 → False) ∨ True) ∨ True) ∧ p1)) ∨ (True ∨ ((p4 → p4) ∨ ((p4 → False) ∧ (p2 ∧ p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150576774186659638850212804161 : ((((p1 ∧ (True ∨ p1)) → (p3 ∧ (False → (((p3 ∧ ((p5 ∨ False) ∨ p4)) → p2) ∧ (p1 → p5))))) ∧ True) → ((p3 ∨ True) ∨ (p2 → p5))) := by
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
theorem thm_5_vars_65001580199588707367344429008 : ((p2 ∨ (((True → p1) → False) → (p5 ∧ (((p5 ∨ (p4 ∧ ((p4 → p2) → ((p4 → (p5 ∧ p3)) ∨ p4)))) → p5) → (p1 → p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111089057141203539090120573175 : (((((False ∨ ((p2 → (p5 → p1)) → p2)) ∨ ((p5 ∧ p4) ∧ p3)) ∨ ((True → (p3 ∧ p5)) ∨ ((False ∨ p2) → p4))) ∧ True) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608001838423728201883652328869 : (((((p4 → ((p3 → (True → (p2 ∧ (p4 → (((p5 → p1) ∧ ((p5 ∧ (False ∧ p4)) → p4)) ∧ p1))))) → (p2 ∨ p2))) ∧ p3) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38646972173845445466914062968 : (((((((p1 → (p2 → p2)) ∨ p4) → p4) → p4) → (p4 → (((p4 ∧ (p1 ∧ (False → p2))) → (p3 ∨ p5)) ∧ (p4 ∨ p1)))) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134150670087246154767445921035 : (((((((p2 ∨ (p4 ∧ p1)) ∧ (p2 ∨ (p4 ∨ p1))) ∧ (p3 ∨ p4)) ∨ (p2 ∨ p5)) ∨ (p5 ∧ (p2 → p2))) ∨ True) ∨ ((p1 ∧ False) ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_585724563687303532866263363852 : (((((((p5 ∧ (p4 → (((False → ((p3 ∨ True) ∨ p5)) ∨ True) → (p2 → False)))) → (((True ∨ p4) ∨ p4) ∧ p5)) → p2) ∧ p4) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175048748763361609289891136720 : ((p2 ∧ (((p1 → (p2 ∨ (p2 → p2))) ∧ (p1 → p3)) ∧ (p5 → (p2 → True)))) → (((p5 ∨ (((True → False) ∧ p4) → p5)) → p5) → p5)) := by
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
  let h7 := h5.left
  let h8 := h5.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h9 : (p5 ∨ (((True → False) ∧ p4) → p5)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
    have h13 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h11, we can now drive its conclusion.
    let h14 := h11 h13
    -- False on the left can always be used.
    apply False.elim h14
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h15 := h2 h9
  -- One of the premise coincides with the conclusion.
  exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62063612259524660814030450470 : ((p2 ∧ (True ∧ ((((((p1 ∧ p5) ∨ (p2 → False)) ∨ (((p2 ∨ p4) ∧ p3) ∧ True)) ∨ p4) → (p4 ∧ (True ∧ (p5 ∨ p1)))) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238178155111128761973538416280 : ((True ∨ p4) ∧ (((((p4 ∧ p5) → p4) ∧ p5) → ((p1 ∨ p2) → ((p3 ∨ ((p4 ∨ ((p2 ∧ p5) → p1)) ∨ True)) ∨ (p4 ∧ False)))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721850813439664810498241379336 : ((((p3 ∨ (p5 → (p4 ∧ p1))) → (p2 → (((p1 ∧ ((p1 ∧ (False ∨ ((p1 ∧ p2) ∧ False))) ∨ (p3 ∧ (p5 → p3)))) ∨ p4) ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307502522453779057244033497155 : (p1 ∨ (True → ((p5 → ((p3 ∨ (p3 ∨ (p2 ∨ (p4 ∨ (p2 ∧ p1))))) ∨ ((p4 ∧ p2) → (p5 ∨ p2)))) ∨ (((p2 ∧ p4) → p2) → p5)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171634086997744616686749850346 : ((((p5 ∨ p2) ∧ ((p4 → (p3 ∧ ((p1 ∨ (p3 → p3)) → p5))) ∨ p3)) ∨ True) ∨ (p3 → ((((False ∨ p2) → (True ∧ False)) ∧ True) → True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326949426926788542022937667240 : (True → ((((p4 ∨ (p4 ∧ (p5 ∧ ((False → (True ∧ p1)) ∨ (((False ∨ (p5 → p4)) ∧ (p4 ∨ p1)) ∨ False))))) ∧ p2) ∨ (p1 ∨ p4)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147158460631332110540174505677 : (((p4 ∧ (((p2 ∧ (False ∨ (False → ((p1 ∧ False) ∧ (p1 ∧ True))))) ∧ p5) ∨ ((False ∨ p2) ∨ p1))) ∧ p3) ∨ (True ∧ (False ∨ (False → p3)))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141319926726998394721719280632 : ((((p3 ∧ (p2 ∨ True)) ∧ True) ∨ ((p5 ∧ ((p2 → p5) ∨ (True ∧ p2))) ∧ ((((p5 ∨ p2) → False) ∧ p2) ∧ p1))) → ((p4 ∧ p1) ∨ p3)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h11.left
      let h16 := h11.right
      -- Conjunctions on the left can always be decomposed.
      let h17 := h15.left
      let h18 := h15.right
      -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
      have h19 : (p5 ∨ p2) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h12
      -- We have shown the premise of h17, we can now drive its conclusion.
      let h20 := h17 h19
      -- False on the left can always be used.
      apply False.elim h20
    case inr h21 =>
      -- Conjunctions on the left can always be decomposed.
      let h22 := h21.left
      let h23 := h21.right
      -- Conjunctions on the left can always be decomposed.
      let h24 := h11.left
      let h25 := h11.right
      -- Conjunctions on the left can always be decomposed.
      let h26 := h24.left
      let h27 := h24.right
      -- We want to use the implication h26 based on <expert-advice>. So we show its premise.
      have h28 : (p5 ∨ p2) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h12
      -- We have shown the premise of h26, we can now drive its conclusion.
      let h29 := h26 h28
      -- False on the left can always be used.
      apply False.elim h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112106167864254869050020353162 : ((((p1 ∨ p5) → (p2 → (((((p4 ∧ (p3 ∧ p1)) ∨ (p3 → True)) → (p3 ∧ p4)) ∨ ((p2 → p4) ∨ p5)) → p3))) ∨ p4) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125207004502431631907946906626 : (((False ∨ (True → True)) ∨ ((p4 ∨ (((p4 ∧ (p4 ∨ (p3 → (((False ∨ (p2 → p5)) → p1) ∨ p5)))) ∧ p1) ∨ p3)) ∧ p4)) → (p5 ∨ True)) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Conjunctions on the left can always be decomposed.
        let h13 := h11.left
        let h14 := h11.right
        -- Disjunctions on the left can always be decomposed.
        cases h14
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47195508277079861953945078566 : ((((False ∨ (p4 ∧ ((((p4 → p3) → True) → (p5 ∨ p5)) ∧ p2))) ∨ (True ∨ ((p3 ∧ (p2 ∧ (p3 ∨ p5))) ∨ p5))) ∨ (p4 ∨ p1)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150213715063599471383963614345 : ((p2 → (((p4 ∧ False) ∧ p5) ∨ (((p3 ∨ p3) ∨ (p1 ∧ ((False ∧ p3) → p1))) → ((p4 → True) ∧ False)))) ∨ (p2 ∨ (p1 ∨ (False → True)))) := by
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
theorem thm_5_vars_213896021881304020920847799418 : (((p4 ∨ (p2 ∧ p1)) ∨ p4) ∨ ((p5 ∨ p4) → (True → (((p2 ∨ p4) → (False ∨ (p4 ∧ (p4 → False)))) ∨ (False → (p1 → (p5 → True))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- Implications on the right can always be decomposed.
    intro h10
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148760006650387478992131822179 : (((p1 → (((p4 → True) → p3) → p4)) ∧ (p3 ∧ (((p2 → p3) ∨ ((p3 ∨ (p1 ∨ False)) → False)) ∨ p3))) ∨ ((True ∨ True) → (p3 → p3))) := by
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
theorem thm_5_vars_193397956377172276304374687274 : (((p3 ∧ p3) ∧ ((False → (True ∧ (False ∧ False))) ∨ p2)) → (((p5 ∨ (p5 ∨ ((p4 ∧ p3) ∨ ((p3 ∨ p5) ∨ True)))) → (p3 → p1)) → p1)) := by
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h8 : (p5 ∨ (p5 ∨ ((p4 ∧ p3) ∨ ((p3 ∨ p5) ∨ True)))) := by
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
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h9 := h2 h8
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h11 := h9 h10
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h13 : (p5 ∨ (p5 ∨ ((p4 ∧ p3) ∨ ((p3 ∨ p5) ∨ True)))) := by
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
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h14 := h2 h13
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h15 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h16 := h14 h15
    -- One of the premise coincides with the conclusion.
    exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231367504156401856687383708223 : (((False → p2) ∨ p3) → ((p4 → (p2 ∧ ((True ∧ ((p4 → ((p2 ∧ (p5 → p3)) ∨ (False → (p1 ∧ False)))) ∧ p2)) ∨ (p2 → p3)))) ∨ True)) := by
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
theorem thm_5_vars_326867289262785294079774323039 : (True → (((((((p5 ∧ ((p3 ∧ p3) → ((p2 ∧ True) → p4))) ∨ p5) → ((p4 ∧ (p5 → p5)) → p3)) ∨ (p5 ∧ p2)) → False) ∨ p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114385043013189279159961780207 : ((((p5 ∧ (p4 ∧ (p5 ∨ (p5 → ((p5 → False) ∨ (p4 ∨ (p3 ∧ True))))))) ∧ (False ∨ False)) ∨ ((p2 ∧ False) ∧ (p3 ∧ False))) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_70910915776654240912049939503 : ((((p3 ∧ ((p2 ∨ p2) ∨ ((p5 ∧ p5) → (True → False)))) ∧ ((((p4 ∨ p1) ∨ p5) ∨ ((True ∧ True) → (False → p3))) ∧ p5)) ∧ p4) → p2) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h5.left
      let h11 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- Disjunctions on the left can always be decomposed.
          cases h13
          case inl h14 =>
            -- One of the premise coincides with the conclusion.
            exact h9
          case inr h15 =>
            -- One of the premise coincides with the conclusion.
            exact h9
        case inr h16 =>
          -- One of the premise coincides with the conclusion.
          exact h9
      case inr h17 =>
        -- One of the premise coincides with the conclusion.
        exact h9
    case inr h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h5.left
      let h20 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h21 =>
        -- Disjunctions on the left can always be decomposed.
        cases h21
        case inl h22 =>
          -- Disjunctions on the left can always be decomposed.
          cases h22
          case inl h23 =>
            -- One of the premise coincides with the conclusion.
            exact h18
          case inr h24 =>
            -- One of the premise coincides with the conclusion.
            exact h18
        case inr h25 =>
          -- One of the premise coincides with the conclusion.
          exact h18
      case inr h26 =>
        -- One of the premise coincides with the conclusion.
        exact h18
  case inr h27 =>
    -- Conjunctions on the left can always be decomposed.
    let h28 := h5.left
    let h29 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h28
    case inl h30 =>
      -- Disjunctions on the left can always be decomposed.
      cases h30
      case inl h31 =>
        -- Disjunctions on the left can always be decomposed.
        cases h31
        case inl h32 =>
          -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
          have h33 : (p5 ∧ p5) := by
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- One of the premise coincides with the conclusion.
            exact h29
            -- One of the premise coincides with the conclusion.
            exact h29
          -- We have shown the premise of h27, we can now drive its conclusion.
          let h34 := h27 h33
          -- We want to use the implication h34 based on <expert-advice>. So we show its premise.
          have h35 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h34, we can now drive its conclusion.
          let h36 := h34 h35
          -- False on the left can always be used.
          apply False.elim h36
        case inr h37 =>
          -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
          have h38 : (p5 ∧ p5) := by
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- One of the premise coincides with the conclusion.
            exact h29
            -- One of the premise coincides with the conclusion.
            exact h29
          -- We have shown the premise of h27, we can now drive its conclusion.
          let h39 := h27 h38
          -- We want to use the implication h39 based on <expert-advice>. So we show its premise.
          have h40 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h39, we can now drive its conclusion.
          let h41 := h39 h40
          -- False on the left can always be used.
          apply False.elim h41
      case inr h42 =>
        -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
        have h43 : (p5 ∧ p5) := by
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h29
          -- One of the premise coincides with the conclusion.
          exact h29
        -- We have shown the premise of h27, we can now drive its conclusion.
        let h44 := h27 h43
        -- We want to use the implication h44 based on <expert-advice>. So we show its premise.
        have h45 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h44, we can now drive its conclusion.
        let h46 := h44 h45
        -- False on the left can always be used.
        apply False.elim h46
    case inr h47 =>
      -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
      have h48 : (p5 ∧ p5) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h29
        -- One of the premise coincides with the conclusion.
        exact h29
      -- We have shown the premise of h27, we can now drive its conclusion.
      let h49 := h27 h48
      -- We want to use the implication h49 based on <expert-advice>. So we show its premise.
      have h50 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h49, we can now drive its conclusion.
      let h51 := h49 h50
      -- False on the left can always be used.
      apply False.elim h51



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62930862501080100457893540935 : ((p4 ∧ (p2 ∧ ((p1 ∧ ((p5 → ((False ∧ ((False → ((p4 ∨ (True → True)) ∨ p3)) → p3)) → p3)) ∨ (False ∨ (p5 ∧ p3)))) → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66116377588511222761537092561 : ((p5 ∨ ((p4 ∧ ((((p4 ∧ p1) ∧ p5) → p5) ∨ (p2 ∧ (p3 → (p2 ∨ (((p4 → p3) ∨ ((p5 → p3) ∨ p5)) ∧ p3)))))) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118499887402292578448576495209 : ((p3 ∨ ((p4 → (((((True ∧ False) → p5) → p5) ∨ (p3 → False)) ∨ False)) → ((p4 ∧ True) → ((False ∨ p5) ∨ (p5 ∨ p2))))) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165752461422547015633519439959 : (((p3 ∧ (True ∨ (p1 → True))) ∨ ((((p3 → True) ∧ (False ∨ True)) → p2) ∧ (p3 ∨ p3))) ∨ (((p1 ∧ ((True ∧ False) ∧ p2)) ∧ True) → p1)) := by
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
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774733485150227362235621085605 : (((False ∨ ((((False ∧ (p1 ∨ p2)) → p4) ∨ (p4 ∨ p2)) → ((((False ∧ p1) ∨ (p4 ∨ (((False ∧ p5) ∨ p1) → p3))) ∨ p4) ∨ True))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_202881708219081880840932045224 : (((p2 ∧ p3) ∨ (p2 ∨ (p1 → True))) ∧ (((p5 ∨ ((p3 ∧ p2) → p3)) → p1) ∨ ((False ∨ p1) → ((True ∧ ((p2 ∧ False) → p2)) ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51629234266136646453384125250 : ((((p3 → ((p2 ∧ p5) ∨ (((p4 ∧ p3) → (True ∨ p1)) ∧ (p1 → p2)))) ∧ p1) ∧ (False ∧ (True ∨ (p4 ∧ (p4 → (p2 → p5)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_732885186998970451517375602767 : ((((p2 ∧ p1) ∧ ((((p5 → ((False ∧ p2) → p4)) → p5) ∧ (p2 ∨ ((p4 ∧ ((True → p1) ∨ p5)) → False))) ∨ ((True ∨ p5) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115130754173291704133215407141 : ((((True ∨ (p4 → False)) ∧ ((p5 ∧ p1) ∧ ((p2 → p1) → p2))) → (((p5 ∨ (p4 → p1)) → (p3 ∨ False)) ∨ (False ∨ p5))) ∨ (p4 ∧ p5)) := by
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
    let h5 := h3.left
    let h6 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h3.left
    let h11 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256032782850214061371876303590 : ((True ∨ p4) → ((((p5 → p4) → p4) ∧ (((p4 ∧ (((p2 → False) ∧ p1) ∧ ((p3 ∧ p3) ∨ p1))) → ((False ∧ p5) ∨ p1)) ∧ p4)) ∨ True)) := by
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
theorem thm_5_vars_47046828953816855590657518550 : ((((True ∧ ((p1 ∨ (((p2 ∨ p5) → ((True ∨ ((p2 ∧ (p3 → p3)) ∨ p3)) → p2)) → p2)) ∧ True)) ∧ (False ∨ p5)) ∨ (False → p2)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246093790416786430647133839110 : ((p4 ∧ p1) ∨ (((p5 → (((p2 ∨ p2) ∨ p4) ∨ p5)) ∧ (p2 → (True ∨ False))) ∨ (p4 ∧ ((((p2 ∧ p5) ∨ (False → p2)) → p1) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314761664798074885119284264702 : (p3 ∨ ((p3 → (((((p4 ∨ p3) ∨ (True ∧ p1)) ∧ p3) → p5) → (p2 ∨ p4))) ∨ ((p2 → (((p3 ∨ p2) → p5) ∧ (p3 ∨ p4))) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234817981067754855092474194713 : ((p5 → (False ∨ False)) → ((((p1 ∨ p1) → False) ∧ (p5 ∨ p5)) ∨ (True → ((p2 ∧ p5) → ((((False ∨ p5) → (p2 ∧ True)) ∨ p4) → p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h3.left
    let h7 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h3.left
    let h10 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_775612469069102741191847833871 : (((False ∨ (False ∨ (((((p5 → p1) ∧ (p3 → (p4 → p4))) ∧ (True → p5)) → True) → (((((p4 → p3) ∨ p2) ∧ p1) → p1) → False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_782270970324930652081225313583 : (((p3 ∨ ((p3 ∧ ((((p2 ∨ (False ∨ p2)) ∧ (p1 → False)) ∧ ((((p3 ∨ True) ∧ (p3 ∨ p3)) ∧ p1) ∧ p1)) ∨ (p1 ∧ True))) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193775532197668348525666750464 : ((p4 ∧ ((((True ∨ True) ∨ (p1 ∨ p2)) → False) ∨ p5)) → ((((p5 ∨ p1) ∨ p3) ∨ (((p1 ∨ p4) ∨ p4) ∧ False)) ∨ (p3 ∨ (p2 → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : ((True ∨ True) ∨ (p1 ∨ p2)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699364783676373697418433973362 : ((((((p5 ∨ p5) → ((p1 ∨ (p4 ∧ (p3 ∧ p4))) ∧ p5)) ∧ p4) → (p1 → ((p3 → p5) ∨ (p3 ∨ (False → (False → (False ∨ p2))))))) ∨ p5) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263803335258445424934994620206 : (True ∧ ((((p3 ∧ p2) ∨ p5) ∨ (((False ∨ ((False → False) ∧ (p5 → p3))) ∧ p3) ∧ p1)) ∨ ((False ∨ True) → ((p3 ∧ (True ∨ p4)) → p3)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- One of the premise coincides with the conclusion.
      exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59290569413398248198513140943 : (((p3 ∨ p4) ∨ (((False ∧ p4) ∧ (p3 ∨ ((True ∧ p3) → ((p1 → False) ∧ p4)))) ∨ (p5 ∧ (False → ((p2 ∨ (p2 ∨ False)) → True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356384894749915894838201620011 : (p5 → ((((p1 → ((True ∧ p2) → p5)) → p3) → (p4 → ((p2 → p3) → True))) → ((((p3 → (p3 ∧ False)) → p4) ∨ p5) ∨ (False → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_733982720973216795617384366484 : ((((True ∨ p1) ∧ ((p1 ∨ (((False → p1) ∧ (((True ∧ (p5 ∨ False)) → p2) ∧ (p3 ∨ (((False → False) ∧ p5) ∨ p5)))) ∧ p5)) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45434586383147064127010101535 : (((True ∨ (((((p3 ∧ p4) → (p4 ∧ (p1 ∨ p1))) ∧ ((p3 ∧ p2) ∨ (True → False))) ∨ (False → (p1 → p3))) ∨ (p5 → p1))) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191492323096458275169572410043 : ((True ∧ (False ∨ ((p2 ∨ True) ∧ (False ∨ (p1 ∨ False))))) ∨ ((((False → p2) ∧ p5) → (True ∨ True)) ∨ (p5 ∧ (((p5 ∧ p2) ∧ True) ∧ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125131178790366030815727716871 : ((((False → p5) ∧ p4) ∨ ((((p5 → p3) ∨ (True ∨ True)) ∧ ((p3 ∧ p1) ∧ p3)) ∨ ((p1 ∧ (p2 → False)) → (p2 ∨ True)))) → (p5 → p5)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h9.left
        let h12 := h9.right
        -- Conjunctions on the left can always be decomposed.
        let h13 := h11.left
        let h14 := h11.right
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h16 =>
          -- Conjunctions on the left can always be decomposed.
          let h17 := h9.left
          let h18 := h9.right
          -- Conjunctions on the left can always be decomposed.
          let h19 := h17.left
          let h20 := h17.right
          -- One of the premise coincides with the conclusion.
          exact h2
        case inr h21 =>
          -- Conjunctions on the left can always be decomposed.
          let h22 := h9.left
          let h23 := h9.right
          -- Conjunctions on the left can always be decomposed.
          let h24 := h22.left
          let h25 := h22.right
          -- One of the premise coincides with the conclusion.
          exact h2
    case inr h26 =>
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233660351592248374078736054230 : ((p2 ∨ (p4 ∨ p1)) → (((p5 ∧ p4) ∨ (p2 ∨ (((p3 ∨ (p2 → p5)) ∨ (p5 ∨ p2)) ∨ True))) → (p2 → ((p5 ∨ (p3 ∨ p2)) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h5
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h13 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h12
        case inr h16 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h12
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
          -- Disjunctions on the left can always be decomposed.
          cases h19
          case inl h20 =>
            -- Disjunctions on the left can always be decomposed.
            cases h1
            case inl h21 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h20
            case inr h22 =>
              -- Disjunctions on the left can always be decomposed.
              cases h22
              case inl h23 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- One of the premise coincides with the conclusion.
                exact h20
              case inr h24 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- One of the premise coincides with the conclusion.
                exact h20
          case inr h25 =>
            -- Disjunctions on the left can always be decomposed.
            cases h1
            case inl h26 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h26
            case inr h27 =>
              -- Disjunctions on the left can always be decomposed.
              cases h27
              case inl h28 =>
                -- Show the left disjunct based on <expert-advice>.
                apply Or.inl
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- One of the premise coincides with the conclusion.
                exact h3
              case inr h29 =>
                -- Show the left disjunct based on <expert-advice>.
                apply Or.inl
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- One of the premise coincides with the conclusion.
                exact h3
        case inr h30 =>
          -- Disjunctions on the left can always be decomposed.
          cases h30
          case inl h31 =>
            -- Disjunctions on the left can always be decomposed.
            cases h1
            case inl h32 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h31
            case inr h33 =>
              -- Disjunctions on the left can always be decomposed.
              cases h33
              case inl h34 =>
                -- Show the left disjunct based on <expert-advice>.
                apply Or.inl
                -- Show the left disjunct based on <expert-advice>.
                apply Or.inl
                -- One of the premise coincides with the conclusion.
                exact h31
              case inr h35 =>
                -- Show the left disjunct based on <expert-advice>.
                apply Or.inl
                -- Show the left disjunct based on <expert-advice>.
                apply Or.inl
                -- One of the premise coincides with the conclusion.
                exact h31
          case inr h36 =>
            -- Disjunctions on the left can always be decomposed.
            cases h1
            case inl h37 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h37
            case inr h38 =>
              -- Disjunctions on the left can always be decomposed.
              cases h38
              case inl h39 =>
                -- Show the left disjunct based on <expert-advice>.
                apply Or.inl
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- One of the premise coincides with the conclusion.
                exact h36
              case inr h40 =>
                -- Show the left disjunct based on <expert-advice>.
                apply Or.inl
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- One of the premise coincides with the conclusion.
                exact h36
      case inr h41 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h42 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h42
        case inr h43 =>
          -- Disjunctions on the left can always be decomposed.
          cases h43
          case inl h44 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h3
          case inr h45 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354747335733317576815148254656 : (p5 → (((p5 ∧ (((False ∨ (p4 ∨ (False → p5))) ∧ (((True ∧ True) ∧ p2) → p4)) → p3)) ∨ ((((p5 ∨ p4) → p3) ∧ p2) → True)) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329657925818461910271715676009 : (True → ((p5 ∧ True) → (((p5 ∧ (p4 ∨ p5)) ∧ (p4 ∨ ((p5 ∧ (p1 → (False ∨ (p1 ∧ (p1 → (p3 → False)))))) ∨ p1))) ∨ (True ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141289565550073380982041660967 : ((((p1 → p3) ∨ (p2 → p1)) ∧ (False ∨ (((p2 → (p1 ∧ (((True ∧ False) ∧ False) ∧ p4))) ∧ p2) ∧ (p4 ∧ True)))) → ((p5 ∨ p5) → p1)) := by
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
      cases h5
      case inl h7 =>
        -- False on the left can always be used.
        apply False.elim h7
      case inr h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Conjunctions on the left can always be decomposed.
        let h11 := h9.left
        let h12 := h9.right
        -- Conjunctions on the left can always be decomposed.
        let h13 := h10.left
        let h14 := h10.right
        -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
        have h15 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h12
        -- We have shown the premise of h11, we can now drive its conclusion.
        let h16 := h11 h15
        -- We need to get the left conjuct of h16 based on <expert-advice>.
        let h17 := h16.left
        -- One of the premise coincides with the conclusion.
        exact h17
    case inr h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h19 =>
        -- False on the left can always be used.
        apply False.elim h19
      case inr h20 =>
        -- Conjunctions on the left can always be decomposed.
        let h21 := h20.left
        let h22 := h20.right
        -- Conjunctions on the left can always be decomposed.
        let h23 := h21.left
        let h24 := h21.right
        -- Conjunctions on the left can always be decomposed.
        let h25 := h22.left
        let h26 := h22.right
        -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
        have h27 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h24
        -- We have shown the premise of h18, we can now drive its conclusion.
        let h28 := h18 h27
        -- One of the premise coincides with the conclusion.
        exact h28
  case inr h29 =>
    -- Conjunctions on the left can always be decomposed.
    let h30 := h1.left
    let h31 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h30
    case inl h32 =>
      -- Disjunctions on the left can always be decomposed.
      cases h31
      case inl h33 =>
        -- False on the left can always be used.
        apply False.elim h33
      case inr h34 =>
        -- Conjunctions on the left can always be decomposed.
        let h35 := h34.left
        let h36 := h34.right
        -- Conjunctions on the left can always be decomposed.
        let h37 := h35.left
        let h38 := h35.right
        -- Conjunctions on the left can always be decomposed.
        let h39 := h36.left
        let h40 := h36.right
        -- We want to use the implication h37 based on <expert-advice>. So we show its premise.
        have h41 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h38
        -- We have shown the premise of h37, we can now drive its conclusion.
        let h42 := h37 h41
        -- We need to get the left conjuct of h42 based on <expert-advice>.
        let h43 := h42.left
        -- One of the premise coincides with the conclusion.
        exact h43
    case inr h44 =>
      -- Disjunctions on the left can always be decomposed.
      cases h31
      case inl h45 =>
        -- False on the left can always be used.
        apply False.elim h45
      case inr h46 =>
        -- Conjunctions on the left can always be decomposed.
        let h47 := h46.left
        let h48 := h46.right
        -- Conjunctions on the left can always be decomposed.
        let h49 := h47.left
        let h50 := h47.right
        -- Conjunctions on the left can always be decomposed.
        let h51 := h48.left
        let h52 := h48.right
        -- We want to use the implication h44 based on <expert-advice>. So we show its premise.
        have h53 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h50
        -- We have shown the premise of h44, we can now drive its conclusion.
        let h54 := h44 h53
        -- One of the premise coincides with the conclusion.
        exact h54



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346897613486988514922674839682 : (p3 → ((((True → (True ∨ (p5 → p1))) → (((p5 → ((p5 ∨ p3) ∧ p1)) ∨ True) ∧ False)) ∨ p1) ∨ (p3 ∧ ((p1 → (p2 ∨ p1)) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_926287650848773765296712006298 : ((((((p1 ∨ (p1 ∧ ((p3 ∨ p2) ∧ p4))) ∧ False) ∨ (True → True)) → (((p1 → ((True ∨ p5) ∨ p4)) ∨ ((False ∧ p3) ∨ p5)) ∧ False)) → False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p1 ∨ (p1 ∧ ((p3 ∨ p2) ∧ p4))) ∧ False) ∨ (True → True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684950822790346685606920479768 : ((((p2 ∧ (p2 ∧ (p5 → ((p2 ∧ (p2 → ((p5 → p3) ∧ p5))) → ((p4 ∨ False) ∨ p5))))) ∨ ((p3 ∧ p5) ∨ (p3 → (p4 ∨ p3)))) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_126485225889868572092528833819 : ((p2 ∧ ((p3 → ((((True → False) ∧ p1) ∨ p4) ∨ (p4 → p4))) → (((((p4 → p1) ∨ p4) → p3) ∧ p3) ∨ (p2 ∧ False)))) → (p3 ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p3 → ((((True → False) ∧ p1) ∨ p4) ∨ (p4 → p4))) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h4
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260657884017355656039241582847 : ((p3 → p3) → ((((((p3 → ((p1 → p2) ∧ True)) → p1) ∧ (p1 ∧ p5)) ∧ (p3 ∨ ((p3 ∨ (False → p5)) ∨ p5))) ∨ p4) ∨ (p3 → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44839788049280426350263395532 : (((((p5 ∨ False) ∨ p5) ∨ ((((p2 → p2) ∨ p3) ∨ ((((p1 ∧ (p4 ∨ (p2 ∨ p1))) ∨ p3) ∧ False) ∨ True)) ∨ (p4 ∧ False))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606719791981557124892078239063 : (((((((True ∨ (p1 ∨ (p4 ∨ (((((p4 ∨ p1) ∧ False) ∨ p4) ∨ (p4 ∧ p1)) → (p3 → p5))))) → False) ∨ (p1 ∧ p4)) ∧ False) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_184622932639295549636105773813 : ((((False ∧ True) ∨ (False ∨ (p5 ∨ p1))) ∧ ((p4 ∨ p2) ∨ p1)) ∨ (p4 → (p4 → (((False ∨ True) → True) ∨ (((p4 ∨ p5) ∧ p5) ∧ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53781970517928654117993545343 : ((((p2 ∧ ((((p2 → p2) ∧ p2) ∨ p2) ∧ p1)) ∨ p2) ∨ ((p2 ∨ (p1 ∧ ((p1 ∨ (p5 ∧ (p4 ∧ p4))) → True))) → (True ∨ False))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341730592738461004858119772730 : (p2 → (((p2 → (p3 ∨ p5)) ∨ ((((p4 ∨ ((False ∧ False) ∧ True)) → False) → ((False → p4) ∨ p4)) → ((True → p1) → p3))) ∨ (False → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208959920000246064596820424373 : ((True ∨ ((p1 → (p4 → p4)) → p4)) → ((p3 ∨ p2) → ((((p1 → ((p4 ∨ p3) ∧ False)) ∨ (p4 ∨ ((False → True) → p2))) ∨ True) ∨ p3))) := by
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
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135771065597857371836414373075 : ((((p3 → (False ∧ (p2 ∧ ((p3 ∧ p4) ∨ (False ∨ (p5 ∧ p3)))))) ∧ p5) → (p4 → ((p5 ∨ (True ∨ p3)) → p3))) ∨ (p3 → (p2 ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314037297374427137460174075247 : (p3 ∨ (((((p3 → (True ∨ False)) → (p4 → (p2 ∧ (((True ∨ True) ∧ (True → (p4 → (False ∧ p1)))) ∨ False)))) ∧ p1) ∧ p4) → (p3 ∧ p4))) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : (p3 → (True ∨ False)) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h8 := h4 h6
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h9 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h10 := h8 h9
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h15 =>
      -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
      have h16 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h14, we can now drive its conclusion.
      let h17 := h14 h16
      -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
      have h18 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h17, we can now drive its conclusion.
      let h19 := h17 h18
      -- We need to get the left conjuct of h19 based on <expert-advice>.
      let h20 := h19.left
      -- False on the left can always be used.
      apply False.elim h20
    case inr h21 =>
      -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
      have h22 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h14, we can now drive its conclusion.
      let h23 := h14 h22
      -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
      have h24 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h23, we can now drive its conclusion.
      let h25 := h23 h24
      -- We need to get the left conjuct of h25 based on <expert-advice>.
      let h26 := h25.left
      -- False on the left can always be used.
      apply False.elim h26
  case inr h27 =>
    -- False on the left can always be used.
    apply False.elim h27
  -- Conjunctions on the left can always be decomposed.
  let h28 := h1.left
  let h29 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h30 := h28.left
  let h31 := h28.right
  -- One of the premise coincides with the conclusion.
  exact h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258582701645994209381631127744 : ((p5 ∨ p4) → ((((p1 → (p3 ∧ (p5 ∨ ((p4 ∧ p2) ∨ (p4 ∨ False))))) ∨ p2) ∨ ((((p4 → (p3 → p5)) ∧ p3) ∧ p5) ∨ p1)) ∨ True)) := by
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
theorem thm_5_vars_667664864098531129340060058956 : ((((p3 ∧ (True ∧ ((True ∧ p1) → ((True ∧ ((p4 ∨ (p1 ∨ p5)) → p4)) ∧ ((p4 → False) → (p4 ∧ p3)))))) ∧ ((p3 ∧ p1) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_644042268113621309161517776768 : ((((True ∨ (((((True ∧ p5) ∧ False) → ((p1 ∨ p4) ∧ p2)) ∨ (p4 → (p5 → True))) ∨ (((p3 ∨ p2) ∨ (p2 ∨ True)) ∧ p1))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190843920568956415980255418247 : (((((p4 ∨ p1) → (p5 ∧ p2)) ∧ p2) → (p1 → False)) ∨ (p1 → ((((False ∨ p3) → (False → (p3 ∧ p3))) ∨ (p5 ∨ (p1 ∨ p1))) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341774340713168469122657016401 : (p2 → ((p5 → (((False → p2) → p4) → (((p1 → ((((p1 ∨ p3) ∨ (p2 ∨ True)) → p5) → p3)) ∨ True) ∧ (p4 → p2)))) ∨ (p5 ∧ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_169382782888317755863002742000 : (((((False ∨ ((((p1 → p2) ∧ (p1 → False)) ∧ p5) → False)) ∧ p3) ∨ p3) ∨ True) ∧ ((p2 → p5) → (False → (p5 ∧ ((p5 ∨ False) → False))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323794862104806674935578496981 : (p5 ∨ (((False ∧ ((p5 → (True ∧ p1)) ∨ (p4 ∧ p3))) ∨ (p4 ∧ (p1 → (p3 ∨ (p4 ∧ p3))))) ∨ ((p3 → ((p4 ∨ True) ∨ True)) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_175369894774448826245453978342 : ((True → ((((p1 ∨ ((True → (p1 ∧ (False ∨ p4))) → False)) → False) ∧ p2) ∨ p1)) → ((True ∧ (p1 ∨ (p1 → p2))) ∨ (False ∧ (p4 → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704847735468038782596605389593 : ((((p1 ∨ ((p1 → ((p1 → (p5 ∨ p5)) ∧ p1)) ∨ p3)) → (p3 → (((p4 ∧ (p2 ∨ ((p1 ∨ p3) ∨ p3))) ∨ (p2 ∨ p4)) ∨ p3))) ∨ False) ∧ True) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115698600144520126036288445461 : (((p4 → ((False ∨ True) → (p4 → False))) ∨ (p2 → (True ∧ ((p1 ∨ p3) ∨ ((((p5 → p1) → p1) ∧ (p3 ∧ p1)) ∨ True))))) ∨ (p2 → False)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53952761524426164642517044077 : (((p5 → (True ∧ (((p1 ∨ p4) ∧ p4) ∧ (False → p2)))) ∨ (((p1 → True) → p4) → (p2 ∨ (p5 ∨ ((False ∨ (True → p1)) ∨ True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213100321071695621400824977050 : ((((False ∨ p5) ∧ False) ∧ p5) ∨ (((False ∨ (p2 → (p4 ∨ ((p5 ∨ (p2 → p4)) ∧ p1)))) ∨ True) ∨ ((p3 ∨ ((p4 ∨ p4) → False)) ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657152222100765568692846598575 : (((((p5 ∧ (p3 ∧ False)) ∨ ((p2 ∧ p5) ∧ ((((p1 → ((p3 ∧ (p2 ∧ (p5 ∧ p2))) ∧ True)) ∨ True) ∨ p4) ∨ p1))) ∨ (p4 ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303938961730551912905371116434 : (p1 ∨ (((((p3 ∧ (False ∨ p1)) ∨ p3) ∧ p4) ∨ ((p3 → ((p5 ∧ (p4 → p4)) ∧ p5)) → (True ∧ ((False → (p4 → p1)) ∨ False)))) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_9653237949506541154223321982 : ((((p5 → p2) ∧ (((p2 → False) → ((p5 ∧ ((p4 ∨ (((p3 ∨ ((p5 ∧ p5) ∧ True)) ∧ True) ∧ True)) → p1)) ∨ p4)) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68811381562719966525275058694 : ((p4 → ((p2 ∨ ((p2 ∨ p1) ∧ p4)) → ((((p1 ∨ p5) ∨ (False ∧ p3)) ∨ ((True ∧ p4) ∨ ((True ∧ p4) → (False ∧ p1)))) ∨ True))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
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
theorem thm_5_vars_685488556414114333769349330996 : ((((((p3 → (p4 ∧ p2)) ∧ ((p1 → (p2 ∧ True)) ∧ (((False ∧ p4) ∨ p4) → False))) ∧ p3) → (p4 ∨ (p3 ∧ (p5 → (p3 ∨ p3))))) ∨ p1) ∧ True) := by
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
  let h6 := h5.left
  let h7 := h5.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h8 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h9 := h4 h8
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- One of the premise coincides with the conclusion.
  exact h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774722310261443119721025799471 : (((False ∨ ((p5 ∨ (p4 ∧ (p4 ∧ (p2 ∧ (p4 ∧ p4))))) ∨ (((True ∨ (((p3 ∧ p2) → True) ∧ ((p1 → p4) ∨ True))) ∧ p2) ∨ True))) ∨ p2) ∧ True) := by
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



