variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67925167617426795102869537060 : ((p2 → ((p1 → ((((p1 ∨ True) ∧ p1) ∨ p5) → (p5 ∨ p3))) ∨ (((p4 ∨ p4) ∧ ((p2 → p4) → (p5 ∨ (p1 ∧ p1)))) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_628628460715589191464822184802 : (((((p3 ∨ ((p4 ∨ (p1 ∨ ((p4 ∧ True) ∨ (p1 ∧ (False → (p3 ∨ (p4 → p2))))))) → ((p1 → (p4 ∧ False)) → False))) ∧ p4) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244918545613149072251006637036 : ((p1 ∧ p3) ∨ (((True ∧ (p1 ∨ (((((p3 ∨ p3) ∧ p2) ∧ False) → p2) → False))) ∨ ((p2 → True) ∨ (True ∧ ((p5 ∨ True) ∧ True)))) ∨ False)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177941862056005784221646903111 : ((((p3 → (False ∧ p1)) ∧ ((False ∨ (p5 → (p2 ∨ p4))) ∨ False)) ∨ True) ∨ ((((p5 ∧ p5) → (p4 → p2)) ∨ (p4 ∨ p5)) ∧ (p5 ∨ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117235624372404076209899111970 : ((True ∧ (p3 ∧ (((p5 → p3) → True) → (((False ∧ (((p4 → p3) ∧ p3) ∧ p5)) ∨ ((p4 → (p5 → p2)) ∧ p1)) ∨ p5)))) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111852959902434166988108235378 : (((((True → p1) → (((p5 ∧ p2) → (p3 → ((False ∨ p2) → p2))) ∧ ((p3 ∧ p4) → p1))) → ((p4 ∨ p1) ∨ p4)) ∨ True) ∨ (p4 → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_78662713297457592152171160385 : ((((((p1 ∨ ((p5 ∨ True) ∧ True)) → False) ∨ ((p1 ∨ ((p4 → p2) → (p1 ∧ p4))) ∨ p3)) → ((p3 ∧ False) ∧ p3)) ∧ (p5 ∧ p1)) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : (((p1 ∨ ((p5 ∨ True) ∧ True)) → False) ∨ ((p1 ∨ ((p4 → p2) → (p1 ∧ p4))) ∨ p3)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336335498723225969115083550085 : (p1 → ((((p3 ∧ True) → p2) → (((p1 ∨ (p5 ∧ ((p3 ∨ (p5 ∨ True)) → (((p4 → p5) ∧ p4) ∧ p2)))) ∧ (True ∧ p2)) → False)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66225349813264241693858641039 : ((p5 ∨ ((((((p3 ∨ True) ∧ p3) → (False ∨ p4)) → p1) ∨ False) → ((p1 ∨ p5) ∨ ((p3 ∨ p1) → (True ∨ ((p2 → p3) ∨ p3)))))) ∨ p1) := by
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
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160435967611031061147249091089 : (((True → (p3 ∨ ((p1 ∨ p2) ∨ (p2 ∨ ((False → False) ∧ (p4 → p1)))))) ∨ ((p4 ∧ p4) → p5)) → (p5 ∨ ((p5 ∧ (p1 ∧ p5)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156815327598151635558311167190 : (((p2 ∨ ((((p4 → p5) → p1) → p3) ∧ ((p3 ∨ ((p2 ∧ p1) → p3)) ∨ (False ∧ p1)))) ∧ p4) ∨ (p2 ∨ ((p2 → p5) → (p1 → True)))) := by
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
theorem thm_5_vars_178619222013961801100008780529 : ((((((p2 ∧ False) → True) ∧ p2) ∨ p4) → (p3 ∧ ((False ∧ True) ∨ p4))) ∨ (False → (((p3 ∧ (False ∨ p2)) ∨ (p4 ∨ (True ∧ p1))) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337550451488630095691392732038 : (p1 → ((p2 ∧ (((p2 ∨ p1) → ((True → ((p4 → ((p1 ∨ True) ∨ p4)) ∧ (p3 ∧ p5))) → p5)) ∨ False)) ∨ (((p2 ∨ p1) ∨ p1) ∨ p2))) := by
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
theorem thm_5_vars_179345952122065950230131857987 : ((p1 ∨ (p2 ∨ ((((p1 → True) → (p3 ∨ True)) → (p4 ∨ p1)) → p1))) ∨ ((True ∧ ((((p3 → (p4 → p5)) ∨ p1) → p2) → p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67411682774315316848158324325 : ((p1 → (((False ∨ ((True → (True ∨ (True ∧ p5))) ∨ ((True → p2) ∨ (p2 → (p2 → ((p4 ∨ p3) → p1)))))) ∧ p2) ∨ (p3 ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788384560305284318064024611765 : (((p5 ∨ ((((p1 ∧ ((True → True) → ((p5 → p5) → (p4 ∧ p1)))) ∨ ((p1 → False) ∨ (p1 → True))) ∧ ((True ∧ p2) ∧ p4)) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113802922672359836029708188945 : ((((False → p1) → (p5 → ((p5 → (False ∨ ((False ∨ (((p5 → p4) ∧ True) ∧ p2)) ∨ (p3 → False)))) → p4))) → (p4 ∧ False)) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_719468497334015526952572431245 : ((((p1 ∨ (True → (True → p1))) ∨ (p4 ∧ ((p5 → p3) → ((((p4 → (True → p3)) → p1) → p1) ∧ ((True ∧ (p4 → p3)) → False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255084235143995032264953786388 : ((p4 ∧ p2) → (((p3 ∧ (p3 → ((p2 ∧ p1) ∨ p5))) ∧ p3) ∨ ((((p5 ∧ ((p1 ∧ p1) ∧ p2)) → (False ∧ (False → False))) → p1) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167402266726467782653350381663 : ((((p2 → p1) ∨ (False ∨ (p3 → (p5 → (p2 ∧ ((p5 → (True ∨ p1)) ∧ p3)))))) → p4) → (((False ∨ (p4 ∨ (p4 ∨ True))) ∨ True) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654330320734771769306901804800 : (((((((((p4 → (p4 ∨ ((p3 → p4) ∨ p4))) → (p1 ∧ p4)) ∧ p4) ∨ p3) ∨ (False ∧ ((p2 ∧ False) → p4))) ∨ p3) ∨ (False → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178361771361442846779951684953 : (((p2 → (False ∧ ((p2 → (False ∨ p4)) ∨ (p4 ∧ p4)))) ∨ (False ∨ True)) ∨ (p1 → (((True ∨ p3) → ((p4 ∧ p3) → (p4 ∧ p2))) → p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196781802387831109211386843912 : ((((p2 ∨ False) ∧ (True ∧ (True → False))) ∧ False) ∨ (((p5 ∧ (False → ((((p3 ∧ True) ∧ p3) → p5) ∧ p3))) → (p1 → (p2 ∨ p1))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339483158196548414562925426449 : (p1 → (False ∨ (((p5 ∨ (p2 → p1)) → (p1 ∧ (((p3 ∧ (((False ∧ p1) ∨ (p2 → True)) ∨ p2)) ∨ (p4 → (p4 ∧ p4))) ∧ False))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40809713505368017058742749013 : ((((p2 ∨ (((False → ((p4 → p1) ∧ p4)) ∨ (False ∧ p4)) ∧ (((p5 ∨ p5) ∨ (p4 ∧ ((p2 ∨ p5) ∨ p5))) ∨ True))) → p5) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233984167524805811830408083735 : ((p5 ∨ (p5 ∧ p5)) → (((False ∧ (False ∧ p5)) → p1) ∧ (((((p5 ∨ (p3 ∧ (((True → p2) → p4) ∧ True))) → p2) → p2) → p3) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611585423046456233187714824293 : (((((False ∨ ((p2 → p1) → ((p5 → p2) → (((p1 ∧ False) ∨ ((p4 ∧ True) → p2)) → (False ∧ (p1 → (p5 → False))))))) → p5) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51965631524049091534938282779 : ((((p5 ∧ (True → p1)) ∧ ((p5 ∧ (p3 ∧ (((p4 → p1) ∨ True) ∧ p4))) ∧ p2)) ∨ (False ∨ ((True → (True ∨ p2)) → (p5 → p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610340641349070634557546544798 : ((((((((((False ∨ (p5 → p3)) → (p4 ∨ True)) ∨ (p3 → p2)) ∨ (p2 → (((p3 → p3) ∧ p3) ∧ p1))) ∧ True) → p2) → p4) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200050305428677886488972849038 : (((p4 ∨ (p4 ∨ (p5 → p2))) → (p1 ∧ False)) → ((p1 ∨ ((p4 → ((p1 ∨ p1) ∨ False)) → ((p4 ∨ (False ∨ p1)) ∧ (False ∧ p1)))) → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : (p4 → ((p1 ∨ p1) ∨ False)) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h7 : (p4 ∨ (p4 ∨ (p5 → p2))) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h8 := h1 h7
      -- We need to get the right conjuct of h8 based on <expert-advice>.
      let h9 := h8.right
      -- False on the left can always be used.
      apply False.elim h9
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h10 := h4 h5
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66421357061331324871038051202 : ((p5 ∨ (p4 → (((((((False → ((False ∨ ((False ∨ p2) ∨ (p2 ∨ p4))) → p5)) ∨ False) ∧ p1) → (p5 ∨ p2)) ∨ p5) ∨ True) → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_595188466267405295358460194220 : ((((((p1 → ((False ∨ p5) → p4)) → ((p3 → ((p2 ∧ p1) ∧ p1)) ∧ True)) → (((p4 → p2) ∧ (True ∨ True)) → (p3 ∧ p4))) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187403579285936903904031437578 : ((p4 ∧ ((p2 → True) → (((p1 ∧ p4) → (p3 ∨ p1)) → False))) → (((True ∧ False) ∨ p5) ∨ (False ∨ (((p1 ∨ p3) ∧ p4) ∨ (True ∧ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p2 → True) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : ((p1 ∧ p4) → (p3 ∨ p1)) := by
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h11 := h6 h7
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152622915036455714684153861155 : (((p1 ∨ True) ∧ (((False ∨ p2) → (((((p4 → False) ∨ p5) ∧ ((True → p3) ∧ p3)) ∨ True) → p5)) ∧ p2)) → (((p4 ∧ p3) → p5) → p5)) := by
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
    let h6 := h4.left
    let h7 := h4.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h8 : (False ∨ p2) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h9 := h6 h8
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : ((((p4 → False) ∨ p5) ∧ ((True → p3) ∧ p3)) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h11 := h9 h10
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h4.left
    let h14 := h4.right
    -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
    have h15 : (False ∨ p2) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h14
    -- We have shown the premise of h13, we can now drive its conclusion.
    let h16 := h13 h15
    -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
    have h17 : ((((p4 → False) ∨ p5) ∧ ((True → p3) ∧ p3)) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h16, we can now drive its conclusion.
    let h18 := h16 h17
    -- One of the premise coincides with the conclusion.
    exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186896686898557169669405853741 : (((p2 → (p1 ∨ (True ∨ p3))) → (((p3 ∨ p4) ∧ False) ∧ True)) → (p2 → ((p4 ∨ (p5 ∨ ((p5 ∧ ((p1 ∧ p3) → p4)) ∧ p4))) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (p2 → (p1 ∨ (True ∨ p3))) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h3
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317870793898452994054682368116 : (p4 ∨ (((p1 ∧ p4) → (p3 ∨ ((((p5 → True) → ((p3 → p2) ∧ (p2 ∨ True))) ∨ ((False → True) → (True → (p4 ∧ p1)))) ∨ p5))) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_223886159164174311531286035656 : ((p3 ∨ (p2 → True)) ∧ (p2 → (((p2 → (((False ∨ p4) → False) ∧ (True → ((False ∨ False) ∨ False)))) ∧ True) → ((p1 ∧ p1) ∧ (p5 → p4))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h9 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h10 := h8 h9
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- False on the left can always be used.
      apply False.elim h13
  case inr h14 =>
    -- False on the left can always be used.
    apply False.elim h14
  -- Conjunctions on the left can always be decomposed.
  let h15 := h3.left
  let h16 := h3.right
  -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
  have h17 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h15, we can now drive its conclusion.
  let h18 := h15 h17
  -- We need to get the right conjuct of h18 based on <expert-advice>.
  let h19 := h18.right
  -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
  have h20 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h19, we can now drive its conclusion.
  let h21 := h19 h20
  -- Disjunctions on the left can always be decomposed.
  cases h21
  case inl h22 =>
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h23 =>
      -- False on the left can always be used.
      apply False.elim h23
    case inr h24 =>
      -- False on the left can always be used.
      apply False.elim h24
  case inr h25 =>
    -- False on the left can always be used.
    apply False.elim h25
  -- Implications on the right can always be decomposed.
  intro h26
  -- Conjunctions on the left can always be decomposed.
  let h27 := h3.left
  let h28 := h3.right
  -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
  have h29 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h27, we can now drive its conclusion.
  let h30 := h27 h29
  -- We need to get the right conjuct of h30 based on <expert-advice>.
  let h31 := h30.right
  -- We want to use the implication h31 based on <expert-advice>. So we show its premise.
  have h32 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h31, we can now drive its conclusion.
  let h33 := h31 h32
  -- Disjunctions on the left can always be decomposed.
  cases h33
  case inl h34 =>
    -- Disjunctions on the left can always be decomposed.
    cases h34
    case inl h35 =>
      -- False on the left can always be used.
      apply False.elim h35
    case inr h36 =>
      -- False on the left can always be used.
      apply False.elim h36
  case inr h37 =>
    -- False on the left can always be used.
    apply False.elim h37



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336130316693807902186719245737 : (p1 → ((((p3 ∧ p4) ∧ ((((p4 ∧ p2) → True) ∨ (False → False)) ∧ ((((p4 → True) ∨ (p1 ∨ p2)) → True) → (p5 → p4)))) ∨ p1) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113066951431209467227144912148 : (((p3 ∨ ((((((p5 ∨ False) ∧ ((False → p4) ∨ p4)) ∧ p2) → p5) ∨ (((True → p4) ∨ p5) → (p1 ∧ p2))) ∨ p4)) → p2) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135540667751530510282575866048 : (((((((p1 → False) → False) ∨ (p3 ∧ p2)) ∨ p5) → (p1 ∧ (p2 → (p5 ∨ p5)))) ∧ ((p5 ∨ (p3 → True)) ∨ p1)) ∨ ((p2 ∧ False) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54817366014753979800457734432 : (((p5 ∨ ((False ∨ ((p4 ∨ p1) → False)) ∨ p4)) → ((((False ∨ (False ∨ ((True ∨ (True ∧ True)) → p4))) → (p1 ∨ p4)) ∨ p2) ∨ p2)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- False on the left can always be used.
        apply False.elim h6
      case inr h7 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h8 : (True ∨ (True ∧ True)) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h9 := h7 h8
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- False on the left can always be used.
        apply False.elim h12
      case inr h13 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h14
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- False on the left can always be used.
          apply False.elim h15
        case inr h16 =>
          -- Disjunctions on the left can always be decomposed.
          cases h16
          case inl h17 =>
            -- False on the left can always be used.
            apply False.elim h17
          case inr h18 =>
            -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
            have h19 : (True ∨ (True ∧ True)) := by
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h18, we can now drive its conclusion.
            let h20 := h18 h19
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h20
    case inr h21 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h22
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h23 =>
        -- False on the left can always be used.
        apply False.elim h23
      case inr h24 =>
        -- Disjunctions on the left can always be decomposed.
        cases h24
        case inl h25 =>
          -- False on the left can always be used.
          apply False.elim h25
        case inr h26 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172776634169655800442995962881 : (((p3 ∨ p4) → ((((False ∧ True) ∧ (p4 ∧ (p4 ∧ p2))) ∨ (p2 ∨ p1)) ∧ p4)) ∨ (((False ∨ True) ∧ (((False ∧ p4) → p4) ∨ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185379638787206370004561675198 : ((p5 ∧ ((p1 ∨ ((True ∨ p3) ∧ p2)) ∨ ((p1 → p5) ∧ p4))) ∨ ((p4 → (False → ((p2 → False) → p1))) ∨ (((p5 ∧ p2) ∨ p5) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119499948480444955752364309566 : ((p4 → (p2 → (p3 ∧ ((((False → p1) → (((((p4 → p4) → p3) ∨ (False → p1)) ∨ p3) ∨ p3)) ∧ p2) → (p1 → p3))))) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183835943288118946953774306728 : ((((((p4 ∧ True) ∧ (p5 ∨ p1)) ∨ p4) ∧ (p1 → p4)) ∧ p4) ∨ (((False → (((True → False) ∨ False) ∨ (p1 ∧ (True ∧ p1)))) ∨ False) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50882799171748113015572476084 : (((((True ∨ (((p3 ∧ p2) → (True ∨ True)) ∧ ((p3 ∨ p1) ∧ False))) → (p1 ∨ p3)) → False) ∧ ((((True ∨ p5) ∨ p3) ∨ p1) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50679356329107860772547556938 : (((((p1 ∨ (p1 ∧ p2)) ∨ True) ∨ (p1 → (True ∨ (((p1 ∧ p1) → p1) → ((False ∨ p3) ∧ p2))))) → ((p5 ∨ (p4 → False)) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64812912635188623052418150040 : ((p2 ∨ (((p1 ∨ (p1 ∨ (((p4 ∧ True) ∧ False) → (False ∧ (((p1 → p1) ∨ False) → (p5 ∧ (True → (p2 ∧ p2)))))))) ∧ p5) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50089387533525001057635765330 : (((p2 ∧ ((p5 ∧ ((((p4 ∨ True) ∧ (((p1 ∧ False) ∧ (p3 → p1)) → True)) ∧ p3) ∧ False)) ∨ True)) ∧ ((p1 ∧ p3) → (p5 ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147382676061188457648134066805 : ((((p4 ∨ (p2 → (((p1 → p4) ∨ (p3 ∨ p4)) ∧ False))) ∨ (((p2 ∨ p2) → (p5 ∨ p5)) → p4)) ∨ True) ∨ (((p4 ∨ p4) ∧ p3) ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606694371215880896950413999300 : ((((((p3 ∧ ((((p4 ∧ ((p2 ∨ (p2 ∨ p3)) ∨ (p5 → p1))) ∧ (p2 ∧ (p5 ∧ p2))) ∧ p2) ∧ p3)) ∧ (p1 ∧ p1)) ∧ p3) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_717664887033649804563802060447 : ((((p5 → (p5 → (p2 ∨ p3))) ∧ ((p2 ∧ (False ∨ (p1 ∧ (p1 ∧ ((False ∨ (((False ∧ p3) → (p5 → p5)) ∧ p4)) ∧ p5))))) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_90816477288733614901991589531 : (((p3 ∨ p2) ∧ (True → ((p3 ∧ ((p4 ∨ (p3 ∧ p4)) ∧ ((((False ∧ True) ∧ p1) ∨ (p2 → (True ∨ p4))) → (False ∨ False)))) ∧ p2))) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h5
    -- We need to get the left conjuct of h6 based on <expert-advice>.
    let h7 := h6.left
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : (((False ∧ True) ∧ p1) ∨ (p2 → (True ∨ p4))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h12 := h9 h10
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h16 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h17 := h3 h16
    -- We need to get the left conjuct of h17 based on <expert-advice>.
    let h18 := h17.left
    -- We need to get the right conjuct of h18 based on <expert-advice>.
    let h19 := h18.right
    -- We need to get the right conjuct of h19 based on <expert-advice>.
    let h20 := h19.right
    -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
    have h21 : (((False ∧ True) ∧ p1) ∨ (p2 → (True ∨ p4))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h22
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h20, we can now drive its conclusion.
    let h23 := h20 h21
    -- Disjunctions on the left can always be decomposed.
    cases h23
    case inl h24 =>
      -- False on the left can always be used.
      apply False.elim h24
    case inr h25 =>
      -- False on the left can always be used.
      apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123737827721721915358306438564 : ((((p5 → (True ∨ True)) → ((False → (False → p1)) ∧ (True ∧ (p5 ∧ p2)))) ∧ ((((p1 ∧ p2) → True) ∧ (p2 ∧ p2)) ∧ p4)) → (p1 ∨ p5)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h10 : (p5 → (True ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h11
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h12 := h2 h10
  -- We need to get the right conjuct of h12 based on <expert-advice>.
  let h13 := h12.right
  -- We need to get the right conjuct of h13 based on <expert-advice>.
  let h14 := h13.right
  -- We need to get the left conjuct of h14 based on <expert-advice>.
  let h15 := h14.left
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52685773462051534471652187009 : (((p5 ∨ ((((p5 ∨ (p2 ∨ ((p3 ∨ False) ∨ p4))) ∨ False) → p4) ∨ False)) ∨ ((p1 → (True → (p4 ∨ p1))) ∨ ((p3 ∨ p2) → True))) ∨ p2) := by
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
theorem thm_5_vars_652309193684995055050852477383 : ((((p3 ∧ (p2 ∧ (((p5 ∧ (False → (((p1 ∧ (False ∧ (p5 ∨ p3))) → (p4 → p2)) → p2))) ∧ p5) ∧ (p4 ∨ True)))) ∧ (p2 ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147894834360140100307241886880 : ((((((p3 ∧ (p4 ∨ (p5 → (p2 ∧ (p2 → p1))))) → p5) → ((p2 ∨ p2) ∧ p5)) ∨ p5) ∧ (p4 ∨ p4)) ∨ ((p5 ∨ p3) → (p4 ∨ True))) := by
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
theorem thm_5_vars_50318552837945546820810510153 : (((((True ∧ ((False ∨ p2) ∨ False)) ∧ (p5 ∨ (p5 ∧ p3))) ∧ (True ∧ (((p3 ∧ p4) ∧ p4) → p5))) ∨ ((p4 → p4) ∨ (False ∨ p1))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300692935237885992088168194357 : (False ∨ ((p1 ∨ ((p3 → ((p2 → p2) ∨ (True → (p1 → True)))) ∧ ((p3 → (False → p1)) ∧ p5))) ∨ ((((p2 ∨ p2) ∨ p1) ∨ True) ∨ p1))) := by
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
theorem thm_5_vars_308635889570123493664843125037 : (p2 ∨ ((True ∧ ((((p2 → False) → (p2 ∧ p1)) ∨ (True ∨ (False ∨ (((p2 ∨ (p5 ∨ p5)) ∧ (False ∨ p5)) ∨ p2)))) ∧ (p1 → p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748793587743214267870627561599 : ((((p4 → True) → (((True ∧ (p3 ∧ True)) ∨ (p1 ∨ p1)) ∧ ((p3 ∨ (((p1 ∨ p4) ∨ p4) ∧ (p3 → p2))) ∨ ((p1 → p2) ∨ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184484718191601449367373863529 : ((((p1 ∧ ((False ∨ p3) → (p3 ∧ True))) → p3) ∨ (p2 ∧ True)) ∨ (((True ∧ (p5 ∨ (((p4 ∨ p4) → True) → (p4 → True)))) ∧ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167871480743403465752543562079 : (((((p5 ∨ (True ∨ (False → p1))) ∧ True) → (p2 ∧ False)) → (p4 ∨ (p1 → (p4 ∧ False)))) → (((p4 ∧ (p4 ∧ p2)) ∨ True) ∨ (p4 ∧ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310660985900175164039986109083 : (p2 ∨ (((True ∨ (p4 → p4)) ∨ False) → (((p4 ∨ True) → ((p5 → p2) ∧ (p3 ∧ False))) → ((p1 → (p4 ∧ ((p3 ∧ p4) ∧ p5))) ∨ p5)))) := by
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
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h5 : (p4 ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h6 := h2 h5
      -- We need to get the right conjuct of h6 based on <expert-advice>.
      let h7 := h6.right
      -- We need to get the right conjuct of h7 based on <expert-advice>.
      let h8 := h7.right
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h10 : (p4 ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h11 := h2 h10
      -- We need to get the right conjuct of h11 based on <expert-advice>.
      let h12 := h11.right
      -- We need to get the right conjuct of h12 based on <expert-advice>.
      let h13 := h12.right
      -- False on the left can always be used.
      apply False.elim h13
  case inr h14 =>
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134026891752957450431256968528 : ((((((True → (p3 ∧ (p2 ∧ (False → p5)))) ∧ (p5 ∧ (p5 ∨ (((p1 ∧ p5) ∨ p2) ∧ p5)))) → p1) ∨ p1) ∨ True) ∨ (p1 ∨ (p4 → p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_781916295993183265096719224366 : (((p2 ∨ (p2 → (((False → (p2 ∨ p1)) → ((((p2 → p4) ∨ p2) ∧ (p5 → True)) ∧ (False ∧ p4))) → ((False ∧ (p3 ∧ p3)) ∨ False)))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (False → (p2 ∨ p1)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49195396460496510672604331077 : ((((p1 → (p4 ∨ p4)) ∧ (p5 ∧ ((((False ∨ (False ∧ True)) ∧ p3) ∧ True) ∨ ((p5 ∨ (p5 → p1)) → p5)))) ∨ ((False ∨ p5) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258757303698550800614607625329 : ((True → False) → ((((p5 ∨ ((((p1 → (p2 → ((p3 ∧ False) ∨ (p4 → p3)))) ∨ (p1 ∨ p4)) ∧ p1) ∧ False)) ∨ (p2 ∨ p5)) ∨ True) ∧ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227411997244682722086235075350 : (((p5 → True) → False) ∨ (((p5 ∧ ((((True → ((p4 ∧ True) → True)) ∨ p3) ∧ (p2 → (p3 ∨ p4))) ∨ True)) ∨ ((True → p3) ∨ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218659806346356417416988727091 : ((True ∧ (p1 ∧ (p1 → False))) → (((p5 ∨ p5) ∧ ((((True ∨ (p3 ∧ p3)) ∨ (p1 → p4)) → (p3 → (True ∨ p4))) ∨ False)) ∨ (p3 ∧ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217187895557487496497759281427 : ((((False ∨ p2) → p4) ∨ False) → ((((((((p2 ∧ p2) → p5) → (False → p3)) ∧ p1) → (True → p3)) → (p1 ∧ p1)) ∨ (True ∨ p3)) ∧ True)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149871162958400541914957686250 : ((p2 ∨ ((True ∨ ((p2 ∨ (((True ∨ p2) → p4) → (p2 ∧ p5))) ∧ ((p4 → (p3 → p1)) ∨ True))) → p3)) ∨ (((p3 ∧ p4) ∧ False) → p5)) := by
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
theorem thm_5_vars_791032847982295563964575712883 : (((True → (((p5 ∨ (((p2 → False) → p3) → (p3 ∨ (p2 ∧ (False → ((True → (((p1 ∧ p2) → True) → True)) ∧ p3)))))) ∨ p2) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135280681546144715434988198621 : (((False → (((True ∧ (p4 ∨ (p3 → (False ∨ p4)))) ∧ ((False → ((p5 ∧ False) → False)) ∨ True)) ∨ p1)) → (p5 ∧ p4)) ∨ (p2 → (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265777774721491053489509337082 : (True ∧ (p4 ∨ (((True → (((p1 ∧ (True ∧ p3)) ∧ p4) ∨ p3)) ∨ (p1 → True)) ∨ (True → (True ∨ (False → ((False → (p4 → p4)) → p2))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702629359124450297635252092390 : (((((p2 → ((p5 ∨ False) → (False ∧ (True → p3)))) → p3) ∨ ((((p5 → True) ∨ p3) ∧ (p5 ∧ ((p5 ∧ (True ∨ True)) ∧ p3))) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168873469326222330197096165070 : ((p4 ∨ ((((p5 ∨ (p3 ∨ False)) ∧ p5) ∧ p3) ∧ (((p2 → True) → p1) → (p1 ∧ False)))) → (((p5 → (False ∧ p4)) → p2) ∨ (p4 ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h11
      -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
      have h12 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h9
      -- We have shown the premise of h11, we can now drive its conclusion.
      let h13 := h11 h12
      -- We need to get the left conjuct of h13 based on <expert-advice>.
      let h14 := h13.left
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h17
        -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
        have h18 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h9
        -- We have shown the premise of h17, we can now drive its conclusion.
        let h19 := h17 h18
        -- We need to get the left conjuct of h19 based on <expert-advice>.
        let h20 := h19.left
        -- False on the left can always be used.
        apply False.elim h20
      case inr h21 =>
        -- False on the left can always be used.
        apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40390004027994633414846361443 : (((((((p2 ∨ (False → p2)) ∨ ((False ∨ ((p3 → p3) ∨ ((p2 ∧ p4) ∧ p4))) → (False → p5))) ∨ p5) → (p5 ∨ p2)) ∨ p5) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166379335485536236921968343527 : ((False ∨ ((p5 ∨ ((p5 ∧ ((p3 ∨ ((p4 ∧ True) ∧ (p1 ∨ p3))) ∨ p4)) ∨ p1)) ∨ p2)) ∨ (False ∨ (((True → p3) ∧ True) ∨ (True → True)))) := by
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
theorem thm_5_vars_714363429302756788089029701080 : (((((p1 → (p5 ∧ p4)) ∨ (p5 ∧ p1)) → (((p3 → p1) → (((p3 ∨ p5) ∧ (p3 → (p2 ∧ True))) → (False ∨ p2))) ∨ (False ∨ True))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328100185954681340623835916469 : (True → ((((p1 ∧ p5) ∧ (False ∨ (p2 → ((p5 ∨ p3) → ((False → (p1 ∨ (p5 ∨ False))) ∨ (p4 ∧ p1)))))) ∨ p3) ∨ ((p5 → p3) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41981515253299709850395013766 : ((((p3 ∨ p2) ∧ ((False → (((((p1 ∧ (p3 ∧ p4)) → ((True ∧ p3) ∧ p2)) ∧ p3) ∨ (p3 → False)) → (p2 ∧ p2))) → p2)) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_716773766060464705351319971984 : ((((True ∧ (p1 ∧ (p3 ∧ p1))) ∧ ((p4 ∨ (((True ∨ p2) ∧ (((False ∧ p5) → (p4 ∧ p1)) ∧ ((p4 ∨ False) ∧ p2))) → False)) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_807507372917041027202622014392 : (((p4 → ((((True ∨ p2) → (p2 ∨ p5)) ∧ p5) ∨ ((((p5 ∧ ((p1 → p2) ∨ p3)) ∨ p2) → ((p1 → p4) → False)) ∨ (p4 ∨ p2)))) ∨ p2) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789158441292526657728681922302 : (((p5 ∨ (((((((False → False) → (p5 ∨ (p4 → (p3 → (True ∨ p1))))) → (p1 ∧ p2)) ∧ True) → p3) ∨ True) → ((True ∧ p5) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338224332062361933349045169698 : (p1 → (((p5 ∨ ((p3 ∨ p3) ∧ p3)) ∧ p2) ∨ (True ∧ ((True → (p5 ∨ ((((p1 ∨ False) ∨ (p3 → p1)) ∧ True) → (p3 ∧ p1)))) → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113490680749230844106952342573 : ((((False → ((((((True ∨ p5) → p3) ∧ p5) ∧ ((False ∧ p2) ∨ (p4 ∧ False))) ∧ True) ∨ p4)) → (p5 → False)) ∨ (p2 ∨ p5)) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39057518003706567745734989467 : ((((p3 ∧ p2) ∨ (p5 ∨ (((((p2 → (p1 ∨ True)) ∧ ((False ∨ p1) ∧ p5)) ∧ ((True → p4) → (p1 ∨ False))) ∧ p5) ∨ p2))) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49934577436850929734235324210 : ((((p4 → (p3 ∧ ((False → ((True → p2) ∨ (((p1 → (p2 ∨ True)) → p2) → p1))) ∨ True))) → p3) ∧ (p2 ∧ ((p1 → True) → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200056313290360115323320643190 : (((p1 → ((p1 ∧ False) ∨ p3)) → (p2 ∨ False)) → (p3 ∨ (((((((p5 ∧ p3) ∨ p1) ∧ False) ∧ p5) ∨ True) ∧ (True ∨ p5)) ∧ (p4 → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_70397047475975572712955886231 : (((((((((False ∨ (False → (((p3 ∧ p2) ∨ p2) ∨ p4))) ∧ p2) ∨ (True ∨ p1)) → (p4 ∧ True)) → p4) ∨ p4) → (p5 ∧ False)) ∧ p1) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((((((False ∨ (False → (((p3 ∧ p2) ∨ p2) ∨ p4))) ∧ p2) ∨ (True ∨ p1)) → (p4 ∧ True)) → p4) ∨ p4) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : (((False ∨ (False → (((p3 ∧ p2) ∨ p2) ∨ p4))) ∧ p2) ∨ (True ∨ p1)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h7 := h5 h6
    -- We need to get the left conjuct of h7 based on <expert-advice>.
    let h8 := h7.left
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h4
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342222780764840912505337342613 : (p2 → ((True ∨ ((p5 → ((p4 ∧ p3) ∧ (True ∨ (p4 ∧ (((p4 ∧ p3) ∨ False) → (p2 ∧ p2)))))) ∨ p1)) → (((p4 → p3) ∧ p3) → p3))) := by
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
  cases h2
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118650201434235235837012354099 : ((p4 ∨ (p2 ∧ ((p3 ∧ (p4 ∧ ((((p1 → p1) → ((p1 ∧ p3) ∧ ((p1 ∧ p3) → p2))) ∨ (p2 → p2)) → p2))) ∧ p5))) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47413825683648116284715101908 : (((False ∧ ((p3 → p1) → ((p1 ∨ p2) ∨ (((((p2 ∨ (p4 ∨ True)) ∨ (p2 ∨ p4)) ∨ True) ∨ (p4 ∨ p5)) ∨ p5)))) ∨ (p5 → True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68126918883660916998487354904 : ((p2 → (p5 → (((p4 ∧ (((((((p3 → False) → p2) → p2) ∨ p3) → (p2 ∧ (p2 → True))) → (p2 ∧ p1)) ∧ True)) ∨ p4) ∨ p2))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263835365027250555408067416634 : (True ∧ ((((p2 → p2) → p5) ∧ (p1 ∨ ((p4 ∧ ((p3 ∨ p3) ∧ p5)) → (p3 ∨ True)))) → (p5 ∧ (((p3 ∧ p2) ∧ p5) ∨ (False → p2))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : (p2 → p2) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h5
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h9 : (p2 → p2) := by
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h10
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h11 := h2 h9
    -- One of the premise coincides with the conclusion.
    exact h11
  -- Conjunctions on the left can always be decomposed.
  let h12 := h1.left
  let h13 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h13
  case inl h14 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h15
    -- False on the left can always be used.
    apply False.elim h15
  case inr h16 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h17
    -- False on the left can always be used.
    apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150625887987836901567335418937 : (((p3 ∧ (((p2 ∨ (p1 ∧ (p1 ∨ (True ∧ (False ∧ p3))))) → False) ∧ (((p2 ∧ p5) → p5) ∨ p1))) ∧ p2) → ((p5 ∧ p4) ∨ (p1 ∨ p2))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608998811720103757220360043308 : ((((((p4 ∨ (((p4 → (p2 → True)) ∧ p2) → (False ∧ p1))) ∧ ((True ∨ (((p2 → False) ∨ (p3 ∨ p3)) → p3)) ∨ False)) ∨ p2) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_616280475370892256133605964064 : ((((((p1 → ((((True ∨ p3) → p5) ∧ (False → False)) → p4)) → p3) ∨ ((True ∨ (p5 → p5)) → ((p2 → False) ∨ (p3 ∧ p2)))) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_673216834649437168693954085049 : ((((((((p4 ∧ p2) → p4) ∨ (p1 ∨ p2)) ∨ (p3 ∧ True)) → (((True → p4) ∨ p1) ∧ ((p5 ∧ False) ∧ True))) → (True ∧ (p1 → False))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((((p4 ∧ p2) → p4) ∨ (p1 ∨ p2)) ∨ (p3 ∧ True)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



