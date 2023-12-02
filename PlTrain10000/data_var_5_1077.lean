variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218245608783201469355207403193 : (((True ∨ p4) ∨ (True → p3)) → (p2 → ((p5 ∧ p2) → ((p5 → (((p5 → p2) ∨ ((p4 ∨ (p2 ∨ p3)) ∧ p4)) → p1)) ∨ (True ∧ True))))) := by
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
  cases h1
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114160566179913275195153493898 : ((((((p5 ∨ (p1 → (((False ∧ True) ∧ ((False ∨ p5) ∧ p5)) ∨ p5))) ∨ p1) ∨ (p2 ∨ p5)) → False) → ((p3 → p1) → p1)) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63045184463887987675318577265 : ((p5 ∧ ((((p2 ∨ False) → (((True ∧ False) ∧ False) ∧ ((((True → p2) ∧ True) ∧ (True ∨ p3)) ∧ p3))) ∧ (p5 → (False ∨ p2))) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47534004433272452405905738117 : (((p4 ∨ ((p5 ∨ (False ∨ p3)) ∨ (((((True ∧ (p4 ∧ p5)) ∨ True) ∧ p3) → (p2 ∧ p3)) ∧ ((p4 ∧ p3) ∨ False)))) ∨ (p4 → True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_87300112454530874027569594923 : ((((p5 → (p4 ∨ (True ∨ p3))) → False) ∧ ((p2 ∧ (p1 → (True ∧ (((p1 ∨ (p5 → ((p1 ∧ p2) ∨ p1))) ∧ p5) ∧ False)))) → p2)) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p5 → (p4 ∨ (True ∨ p3))) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118464814451446204623340539750 : ((p3 ∨ ((((((p1 ∧ ((p5 → True) ∨ p3)) ∨ True) → p2) ∨ (p2 → ((p3 ∧ p1) ∨ ((True ∨ True) ∧ False)))) ∧ p1) → p5)) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201267970242985562243052879165 : ((p3 → (p1 ∧ (p2 ∧ ((p5 ∨ p3) → True)))) → (p1 ∨ (p1 → (p4 → (((p5 → p1) ∧ p1) ∧ (((p1 → p2) → False) → (p3 → p4))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263076881250063193929120165157 : (True ∧ ((((p4 ∧ (True ∧ (((p1 → (((p2 → p4) → (p4 → p5)) ∧ True)) → p4) ∨ (p1 ∨ (p4 ∧ p5))))) ∧ p3) ∨ p2) ∨ (p3 → True))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181064834405932738738083422374 : (((True ∨ p1) → (((False ∧ (p1 ∧ p5)) ∧ p1) → (p3 ∧ (False ∧ p2)))) → (((p1 ∧ p1) → (p3 → ((p2 ∧ p4) ∨ True))) ∧ (False → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h6
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264660629338439837638371495816 : (True ∧ ((p3 → (p2 ∧ p1)) → (p3 → (((((p5 → False) → True) ∧ (((True ∧ p5) ∨ ((True ∨ False) ∨ p4)) ∨ p3)) → p1) ∨ (p4 → p3))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317783772131101082458720786214 : (p4 ∨ ((((p4 → ((False ∧ ((p4 ∧ (p4 ∨ p5)) ∨ p3)) → p5)) → p2) → ((((True ∧ (p3 → False)) ∨ p1) ∨ False) ∨ (p1 ∧ p1))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53083457160320719164674610948 : (((True ∨ ((False → (p4 ∧ (p2 ∧ (False → p2)))) → (p5 ∧ p3))) ∧ (p4 → (((p5 ∧ False) ∨ False) ∧ ((False ∧ p1) ∨ (True → True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601525721053102190525403930791 : ((((p3 ∧ ((((p2 → p5) → (p5 ∧ (((((p5 ∨ p4) ∧ p2) ∨ p2) ∧ p5) ∧ p4))) ∨ (False ∧ (p1 ∧ p2))) → (p2 ∨ False))) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246359029221276760552886543400 : ((p4 ∧ p5) ∨ (p2 ∨ (((p4 ∨ ((True ∨ p3) → p1)) ∧ ((((((p4 → p5) ∨ False) → True) ∨ p2) ∧ (p5 ∨ (False → p3))) ∧ False)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309799760416616820501894994207 : (p2 ∨ (((True ∧ ((True ∧ p2) ∨ ((False ∨ p3) ∧ p1))) ∧ ((False ∧ ((p4 ∨ p1) ∧ p5)) ∨ (True → p2))) ∨ (((False → p1) → p4) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → p1) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358218406043320807306156400873 : (p5 → (p4 ∨ (((p2 → p4) ∧ (((p4 → False) → (p4 ∨ p1)) ∨ ((p5 ∨ (p4 ∨ (p5 → p3))) → (p1 ∨ (p2 ∨ (True → p1)))))) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46371643483566820638774928816 : ((((((((p3 ∨ (p5 ∧ (True → p4))) → p2) → p4) → True) → False) → ((p5 ∧ (False ∨ ((p5 ∧ False) ∧ p5))) ∨ False)) ∧ (p1 → True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p3 ∨ (p5 ∧ (True → p4))) → p2) → p4) → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234134818950299638978758159843 : ((True → (p4 ∨ p4)) → ((((p1 → ((p2 → p5) → (p5 ∧ (p1 → p1)))) → ((False ∨ ((p3 ∨ False) → p5)) ∧ (p5 ∨ p1))) ∨ True) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190261329415291941065963082800 : ((((((False ∧ (p1 ∨ p2)) ∧ p1) ∨ p1) ∨ False) ∨ True) ∨ ((p3 ∧ (((True ∧ (p2 ∧ (p5 ∨ (p4 ∨ p5)))) ∧ False) ∧ p4)) → (p5 ∧ False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_603182021655686575845422409303 : ((((p2 ∨ ((True ∨ (p5 → (((((p1 → p1) ∧ (((p2 → p5) → (p5 → p3)) ∧ p2)) ∨ p3) → p3) ∨ p1))) → (p2 ∨ p5))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53810433590240507387851857176 : ((((p5 → ((True ∨ p4) ∧ (p1 ∨ (p1 → p2)))) → False) ∨ (p2 → (p4 → ((p3 ∨ (True ∨ p5)) → (p5 ∨ (p2 ∨ (True ∨ False))))))) ∨ p4) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257635539378674503941198902513 : ((p3 ∨ p2) → ((((p1 ∧ p1) → p3) → (p5 ∧ (False → p2))) → (True ∧ (((p4 → ((p3 ∨ p4) → p1)) → (p2 → (p5 ∨ p2))) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186512654818288178645058370045 : (((((((True ∨ p1) ∧ p2) ∨ True) ∧ False) ∧ p4) ∨ (p3 ∨ p5)) → (p1 ∨ (((p3 ∧ (False ∧ (((p1 ∨ p4) ∧ p1) ∧ True))) ∨ p4) ∨ True))) := by
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
    cases h5
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h10 =>
        -- False on the left can always be used.
        apply False.elim h6
      case inr h11 =>
        -- False on the left can always be used.
        apply False.elim h6
    case inr h12 =>
      -- False on the left can always be used.
      apply False.elim h6
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329103059048071627788258809167 : (True → ((((p3 → False) ∧ True) ∨ p1) ∨ (p3 ∨ ((p1 ∨ (p5 ∨ (False → (((True → True) ∧ False) ∧ (((p2 → p1) ∨ False) → p5))))) ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46791994121925625882836762641 : (((p5 → (((((p5 ∨ ((False ∨ (False → (False → p1))) ∨ False)) → p1) ∨ p4) ∨ ((p4 ∧ p5) ∨ True)) ∧ (p3 → False))) ∧ (p2 → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38510829611185048582515893871 : ((((True → ((p4 → p3) ∧ (True ∧ ((p4 → True) ∨ (True ∨ p2))))) ∨ ((True ∧ p3) ∨ ((True ∨ (p2 ∨ p1)) → (False ∨ p5)))) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785049491567783839131195813961 : (((p4 ∨ ((((p5 → True) ∧ (((p3 ∨ ((False → p3) → ((p2 ∨ (((p5 → p1) ∧ True) ∧ p5)) → p1))) ∨ False) → p4)) ∧ True) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241518209223052774894269530191 : ((False → p3) ∧ (((False ∨ (p3 → (p1 ∨ p4))) ∧ ((p1 → (p2 → ((True ∧ ((((p1 → p4) → p2) ∧ p4) ∨ p4)) ∧ p3))) ∧ p3)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44097205711754010929596013881 : ((((p2 → (p1 ∨ ((True → ((((False ∧ p3) ∨ False) → p5) ∨ (True ∨ ((p3 → p2) ∧ False)))) ∧ p2))) ∧ (p3 → (True ∧ p1))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56298240919287186663460925345 : (((((p3 → p4) ∨ p3) ∧ p4) → (True → ((p2 ∧ (False → p1)) ∨ ((p1 ∨ (p5 ∨ (False ∧ (p1 ∨ (p4 → p2))))) ∨ (p2 → p2))))) ∨ p1) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192212595183759367310583771012 : (((((p5 ∧ False) ∨ ((False ∧ p1) → False)) → p5) ∧ p4) → ((p5 ∨ (True → (p1 ∨ (p4 → (p1 ∧ ((False → (True ∧ True)) ∧ p3)))))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p5 ∧ False) ∨ ((False ∧ p1) → False)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h6
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354765433624116367438130133985 : (p5 → ((((p1 ∨ ((False ∧ p3) → ((p5 → p4) ∧ p4))) → (p5 → False)) ∨ (((False ∧ (p1 ∧ (True ∧ p4))) ∧ p1) ∨ (p2 → p2))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135868484401931459767628577788 : ((((p2 → ((p3 ∨ (p4 ∨ p4)) ∧ False)) ∧ (p2 ∨ (True ∧ True))) ∨ (((False ∨ p5) ∨ (p4 ∧ p3)) → (True ∧ p4))) ∨ (True ∨ (p4 ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349564208354346742130075897405 : (p4 → ((((p5 → (True ∧ (p1 ∨ ((p4 ∨ (True ∧ p2)) → ((((p2 ∨ p2) ∧ p1) ∧ p1) ∧ p2))))) ∨ ((True → p2) → p4)) ∨ True) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_202135036340574403809591327337 : ((((p1 → (p4 → True)) → False) → True) ∧ (((p3 ∧ (p1 → True)) ∨ p5) ∨ (((True ∨ p2) → (((p3 → p3) → (p2 → p2)) ∧ p4)) → p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (True ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185371568114327293761782402613 : ((p5 ∧ ((p5 ∨ (p1 ∨ (p2 ∨ (p5 ∨ (p4 ∧ p2))))) ∨ p5)) ∨ (((((False ∧ ((p4 ∧ (p5 ∧ True)) ∨ p4)) ∧ False) → p2) ∧ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344514879100997036990180603582 : (p2 → (True → (p4 ∨ ((((((((p3 ∧ p3) ∨ (p4 ∧ p4)) ∧ (p1 ∧ (p2 ∧ (True ∨ p1)))) ∧ p4) ∧ (p1 ∧ p1)) ∨ True) ∨ True) ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
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
theorem thm_5_vars_68377292171441141027961895668 : ((p3 → ((p1 ∨ ((p5 ∨ p5) ∧ False)) ∧ ((p5 ∨ (p2 ∧ (p5 ∧ ((p5 ∨ p3) ∧ p1)))) ∧ ((p4 → p5) → ((False ∧ False) → p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191932757004361430811379728360 : ((True → ((p3 → ((p3 ∧ p2) → p4)) ∧ (p1 ∨ False))) ∨ (((((True ∧ p2) → (((True ∨ p2) → False) ∨ p1)) ∨ p1) ∨ True) ∨ (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191031665216646330094909287626 : (((((p1 ∨ p4) ∨ p1) ∨ False) → (p1 ∧ (p5 ∨ p3))) ∨ ((True ∨ p3) ∧ (p3 ∨ (False → (True ∧ ((p2 → p2) ∧ (p4 → (p4 ∧ p4)))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607376066694298634104604084706 : ((((((p2 ∨ False) ∧ (((True → p3) ∧ p1) → ((p2 → (True → ((p5 → (p2 → (False ∧ (False ∨ p4)))) ∨ True))) ∨ p1))) ∧ p3) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611730651138118281562202444006 : (((((True → ((p4 ∨ ((((p2 ∧ ((True → (False ∨ True)) → (p5 ∧ False))) ∧ (p1 → False)) ∨ p1) ∨ True)) → (p4 ∨ p1))) → p5) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_55381188605629991755455789776 : (((((p5 → (p4 → p5)) → True) ∧ p5) → ((p5 → (p2 ∧ ((True ∧ p1) ∧ (p1 → p4)))) ∨ ((True ∨ p1) ∨ (p1 → (p4 ∨ True))))) ∨ False) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_778484663041122022542916752533 : (((p1 ∨ (p4 ∧ (p1 ∨ (False ∨ (p2 ∧ (((p1 ∧ p3) ∧ ((p1 ∨ False) ∨ (False ∨ (((p2 → p5) ∧ p4) ∨ p4)))) → (p3 ∨ p1))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40930905003271635244061159281 : (((((p1 ∧ (p1 → (((p1 → ((True ∧ p3) ∨ (((p1 ∨ p1) ∧ (p1 ∨ True)) → p3))) ∧ True) ∧ p1))) ∧ p1) ∨ (True ∨ p3)) ∨ p2) ∨ p3) := by
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
theorem thm_5_vars_112055668004922481182796528688 : ((((p2 ∧ p1) ∧ (((p3 → (p1 ∨ p5)) ∧ (p3 → (p4 ∨ (p2 ∧ p5)))) ∨ (((True → (True ∨ p4)) ∧ p2) ∧ True))) ∨ p1) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117382750188968523056794177524 : ((p1 ∧ ((((((False ∧ p3) ∨ p1) ∧ (True ∨ p2)) ∧ (((True ∨ p5) ∧ (False ∧ (p2 ∨ False))) ∨ p3)) ∧ (p2 → p1)) ∧ False)) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219750840489751537093117926783 : ((p2 → ((False ∨ False) ∧ False)) → (((True → (False ∧ False)) ∧ (((((p4 ∨ p2) ∧ p3) ∧ p5) ∨ ((p1 ∧ False) ∨ (False ∨ p4))) → p2)) → False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309364550106076635252012422240 : (p2 ∨ (((p5 → (p3 ∧ (False ∨ True))) ∨ (((p4 ∧ (((p5 ∨ (p1 ∨ p2)) ∨ True) ∧ True)) → ((p1 ∧ p2) ∨ p5)) ∧ p1)) ∨ (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_86545311918967236952817867886 : ((((p1 ∨ ((p5 → (p5 → p1)) ∧ p5)) ∧ p2) ∧ ((p3 → (True → (((p5 → ((p1 ∨ False) → p3)) ∨ False) ∨ p5))) ∨ (p2 ∨ p4))) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h10 =>
        -- One of the premise coincides with the conclusion.
        exact h6
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h14 =>
      -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
      have h15 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h13
      -- We have shown the premise of h12, we can now drive its conclusion.
      let h16 := h12 h15
      -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
      have h17 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h13
      -- We have shown the premise of h16, we can now drive its conclusion.
      let h18 := h16 h17
      -- One of the premise coincides with the conclusion.
      exact h18
    case inr h19 =>
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h20 =>
        -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
        have h21 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h13
        -- We have shown the premise of h12, we can now drive its conclusion.
        let h22 := h12 h21
        -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
        have h23 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h13
        -- We have shown the premise of h22, we can now drive its conclusion.
        let h24 := h22 h23
        -- One of the premise coincides with the conclusion.
        exact h24
      case inr h25 =>
        -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
        have h26 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h13
        -- We have shown the premise of h12, we can now drive its conclusion.
        let h27 := h12 h26
        -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
        have h28 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h13
        -- We have shown the premise of h27, we can now drive its conclusion.
        let h29 := h27 h28
        -- One of the premise coincides with the conclusion.
        exact h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245012010238294455129971783527 : ((p1 ∧ p4) ∨ ((p3 ∧ p2) ∨ (((((p1 ∨ (((p4 → p5) → False) ∨ p1)) ∨ (True ∧ (p4 ∨ False))) → (p3 → False)) → (p5 ∧ True)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_144557355619171904205751032771 : ((((p4 → (p2 ∧ (True → p4))) → (((True → (p5 ∨ p1)) ∨ ((p5 → False) → True)) ∨ False)) ∨ (p1 → p1)) ∧ (p5 ∨ (False ∨ (False ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136248032199382584072858900781 : (((False ∨ (False ∨ ((False ∧ p5) ∧ p3))) ∨ (p4 ∧ (p5 → (True ∨ (((p3 ∧ p4) → (p1 → p4)) ∨ (p3 → p5)))))) ∨ ((True → False) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350053649809878765764739544147 : (p4 → ((((p5 ∨ (((p5 ∨ ((((p4 ∧ p5) → p1) ∨ (p3 → p2)) ∨ False)) → (p3 ∧ True)) → (False ∨ p5))) ∧ p1) ∧ (p1 ∧ False)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55695129488479773603930603103 : (((((p4 → True) → p4) ∨ p4) ∧ (p3 ∧ ((((True ∧ (p3 ∨ (True ∧ (p5 ∨ (p1 ∧ p2))))) → (p3 ∧ p2)) → False) ∧ (p3 → True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_754403796959644558362068279966 : (((False ∧ ((False ∨ p5) → ((p2 ∨ ((p4 → (p3 ∨ (p3 ∨ (True ∨ p5)))) ∧ ((((p2 ∧ False) ∨ False) ∧ (False → p4)) ∨ True))) ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68111440305153460183098211760 : ((p2 → (p2 → ((p5 ∨ ((((p5 → (False ∨ ((p4 ∧ (True ∧ False)) → True))) ∨ (p3 ∧ True)) ∨ (True → p4)) → p1)) → (True ∧ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165381934498054795635379280623 : (((((p2 ∨ (p5 ∨ False)) → True) ∧ (p3 ∨ ((p4 ∧ True) ∧ p3))) ∨ (p1 → (False ∨ p5))) ∨ (((False → ((p4 ∨ p1) ∨ p5)) → False) → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → ((p4 ∨ p1) ∨ p5)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67802744328160197366585689352 : ((p2 → (((p5 → (((p1 ∨ ((p1 ∨ p1) → p1)) → (p3 ∧ ((p5 → False) ∨ p5))) → p1)) → ((p2 → p5) ∧ (p3 ∧ p2))) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233818552001383749870621462353 : ((p3 ∨ (p4 → p2)) → (((p2 ∧ (p2 → p1)) ∨ ((((((p5 → p1) ∨ False) ∨ p4) ∧ p1) → p1) ∨ (True → p2))) → (False ∨ (p1 → True)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h6 =>
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
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h13
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h15
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h18
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h20
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678292842969769096224402468354 : ((((((p3 → p4) → ((p5 ∨ (p3 ∧ True)) ∧ p3)) ∨ (((((p3 ∧ p5) ∧ p1) → True) ∨ True) ∨ p2)) ∨ (((p2 ∨ p5) ∨ p1) ∨ p2)) ∨ p4) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234025180114478720620911343025 : ((p5 ∨ (True → False)) → ((p1 ∨ (p3 ∧ p1)) ∨ ((p3 → (True ∧ True)) ∨ ((p2 → True) ∨ ((p5 ∧ p2) → (p4 ∧ (p3 → (p3 ∧ p2)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_182763636084085973154398185254 : (((p5 → (True ∨ (p1 → p4))) ∨ (((False ∧ p1) ∨ p3) → p2)) ∧ ((p3 ∧ (((p3 ∨ ((True ∨ p3) → p2)) ∧ p2) → p4)) ∨ (False → p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158896740279751126125763462497 : ((p1 ∨ ((p1 ∨ (((((True → p5) ∨ (False ∧ ((p3 → p4) ∨ True))) ∨ False) → False) ∧ p5)) ∨ p4)) ∨ ((True ∧ p3) ∨ (p5 ∨ (p2 → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48743115756345268932565340120 : (((((p3 ∧ False) → p4) → ((((p2 → (p4 → ((p3 ∧ p2) ∧ p2))) ∧ p5) → (True → (p5 → False))) → p1)) ∧ (p1 ∨ (p2 ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172319800333534558762280888614 : (((p5 → ((p3 ∨ ((p1 ∨ p3) ∨ True)) ∧ p1)) → (p5 ∧ ((p2 → False) → p2))) ∨ ((False → ((p5 → ((p3 ∨ p2) ∨ p5)) ∧ p4)) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113727208942866249898770851815 : (((((p1 ∧ (((p2 ∧ p1) → False) → (((False ∨ (p2 ∨ p1)) → True) → False))) → p5) ∨ (p1 → (False ∧ p1))) → (p5 ∨ True)) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167291350443741281679106549411 : ((((p3 ∨ (p2 ∨ (p5 → (p1 ∨ (((True → True) ∧ (False → p4)) → p5))))) ∨ p3) → p3) → (p4 → (((p3 → p2) ∨ (p1 ∨ False)) → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
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
      -- False on the left can always be used.
      apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39840502231133035376361971155 : (((p1 → (((((p2 → p4) ∧ (True → p1)) → False) → ((False → False) ∧ ((p1 ∧ True) ∧ (p5 ∨ p2)))) → (p4 ∧ (p5 ∨ True)))) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49511179822426909547268305084 : ((((((p4 → (False ∨ (((True ∨ p2) ∧ ((False ∨ p4) → p4)) → p1))) ∧ (p3 ∨ p3)) ∨ p3) ∧ (p4 → p5)) → (p1 → (p1 ∨ False))) ∨ p2) := by
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
    cases h7
    case inl h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h10 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179616491328884718469264291285 : ((p4 → ((p5 ∨ ((p5 → (((p2 ∧ p5) → p1) ∧ False)) → p1)) ∧ p5)) ∨ ((p2 ∨ (p5 ∨ (True → (True ∨ (p1 → (p1 ∨ p3)))))) ∨ p1)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137631157689636944465065498530 : ((False ∨ ((((p2 ∧ True) → (((True ∧ p4) ∧ (False ∧ p3)) ∧ p3)) ∨ ((p1 → (p3 ∧ False)) ∧ p4)) ∨ (False ∨ p4))) ∨ (p1 ∨ (True → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_737280901428866173809764348959 : ((((p4 → p1) ∧ (((p1 → (True ∧ False)) ∧ ((((p4 → True) ∧ p3) ∨ ((p1 ∨ (False ∨ (p5 → p5))) → (p1 ∧ p4))) ∧ p2)) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238735478742351496061169242512 : ((p1 ∨ True) ∧ ((p3 ∧ ((p5 → (False → p3)) ∧ (p5 ∨ (((((p3 → p4) → (False ∧ (p1 ∧ p2))) ∨ True) → p2) → False)))) ∨ (False → p2))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191601010748780959881472430142 : ((p3 ∧ (((p4 → (p4 ∧ (p2 ∧ False))) → False) ∨ p4)) ∨ ((p3 → (True ∧ True)) → (False → ((True ∨ (p4 → p5)) ∧ ((p2 ∧ p1) ∨ True))))) := by
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
theorem thm_5_vars_157820879471662078130011568272 : ((((p2 ∧ ((False → p1) ∧ p5)) ∨ (p2 → (p4 ∧ (p3 ∨ p2)))) → (((p3 ∧ p1) ∨ p2) ∨ p2)) ∨ (p4 → (((p5 ∧ p2) ∧ p3) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116951487675244376038841772886 : (((p2 ∧ p3) → ((p1 ∧ (((p5 ∨ (p4 ∨ ((p1 ∧ (((p1 ∨ p3) → True) ∧ (p4 → p5))) ∨ p3))) ∨ p2) ∨ p5)) ∨ p3)) ∨ (p2 ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_706729468525737748565886541990 : (((((((p1 ∨ (True → p1)) → p1) ∨ p3) ∧ p1) ∨ ((False ∧ p3) ∧ ((p3 ∨ ((False ∧ ((p1 ∧ p1) → False)) ∨ p3)) ∨ (False → p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_718942106833676665470504938139 : (((((True ∨ p3) → (True → p1)) ∨ ((p2 → ((((p3 → True) → p3) ∧ ((((p1 ∨ p4) ∨ p1) → p2) ∨ False)) → p2)) → (p2 ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205168999419173808748943992168 : (((p5 ∧ (True → p5)) ∧ (False ∧ p5)) ∨ ((p2 ∨ (p2 ∨ ((p2 ∧ (((p4 ∨ p3) ∧ p1) ∨ (True ∨ False))) ∨ (p2 → p4)))) ∨ (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657454857290133036848224970501 : (((((p3 ∧ p1) ∨ (p5 ∨ ((((p4 ∧ p2) ∨ p4) ∧ (((True → (p5 ∨ p3)) ∨ (p4 → False)) ∨ (p2 ∨ p3))) ∧ p3))) ∨ (p5 ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156709987540162632421572361403 : (((((True ∨ ((p4 → p3) ∨ (False ∧ (True → p2)))) ∧ p5) → ((p4 ∨ (p3 ∨ p4)) → False)) ∧ p5) ∨ (p4 → (((False ∨ p3) ∧ False) → p5))) := by
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
    apply False.elim h5
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134932463317884846161937288649 : ((((True ∧ (((p4 ∨ (p4 ∧ (False ∧ p4))) → ((True ∧ (p1 → p1)) → (p5 ∨ p3))) → p4)) → p1) ∧ (p2 → p2)) ∨ (False → (False ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64568334532972463914004941972 : ((p1 ∨ (((p2 → p4) ∧ True) ∨ ((((p1 → (p4 ∧ True)) ∧ ((p3 ∨ ((False → p4) → (True ∧ p1))) ∨ True)) → False) → (p3 → p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299459147241504393409500907996 : (False ∨ ((p4 ∨ (((True ∧ True) ∨ p2) → ((((p3 ∨ p3) ∨ True) → (False ∨ p2)) ∨ (p5 → (p5 ∨ (p2 → ((p2 ∨ True) ∧ p3))))))) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135751489865516062394599338211 : ((((p4 ∨ p4) ∨ (p1 ∧ (p5 ∧ ((((p5 → p4) → p2) → p5) ∧ True)))) ∨ (p4 ∨ (p5 → ((p1 → p1) ∧ True)))) ∨ ((False → p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308090810660713024706001632063 : (p2 ∨ ((((p1 ∨ ((p5 → p3) → True)) ∧ (p5 → (((p3 → p2) ∨ (False ∧ False)) ∨ p3))) ∨ (p4 → (((p1 → p5) ∨ p5) ∨ True))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_791385792622829000125027455313 : (((True → ((((((((True → p1) → p1) ∨ False) ∨ (True → True)) → p2) → (p4 ∨ p1)) → ((p2 ∨ p2) → (p1 ∧ (p2 ∧ p2)))) ∨ True)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_427412072997808820565339544128 : ((((((p1 ∨ p2) → (((p1 → ((p5 ∧ False) ∨ ((p1 ∧ (p5 → p2)) ∨ (p4 ∧ p3)))) → (p1 → p5)) ∧ p3)) ∧ True) ∨ (p5 → True)) ∧ True) ∧ True) := by
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
theorem thm_5_vars_207414681947068373990735656785 : (((p5 ∧ (True → (True → True))) ∨ p1) → (((p5 ∧ ((False ∨ (p1 ∨ (False → p2))) ∧ p3)) ∨ p3) ∨ (False → ((True ∨ p4) ∨ (p1 → False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113985069021396201509312661532 : (((p4 ∨ (((p5 ∧ p4) ∨ ((False → (((p4 ∨ (p4 ∧ True)) → True) → False)) ∧ (True → p3))) ∨ False)) ∧ (p4 ∨ (p1 ∨ False))) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_188861384061221044260547077245 : (((p1 ∧ (False ∧ (False ∧ p4))) ∨ (p2 ∨ (p4 ∨ True))) ∧ ((p4 ∧ p3) → ((p2 → (((p1 ∨ p2) → (p5 → False)) ∨ p2)) → (p2 → p4)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694757383086659019187266338405 : ((((p4 ∨ (False ∨ ((p5 ∨ ((p1 → p2) ∧ False)) ∨ ((p5 → p3) ∧ p5)))) ∨ (p5 → ((True ∨ ((p3 → (p1 → False)) ∧ p2)) ∨ False))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_98827724988368231058278247351 : ((True → ((p4 ∨ ((((False ∧ p1) ∨ (p4 ∨ ((True → True) ∧ p5))) ∧ p3) → (p1 → (p4 → (p3 ∧ (False → (p5 ∧ True))))))) ∧ p3)) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_631106770371020567190072568468 : (((((((p3 → p4) ∨ (p3 ∨ (((False ∨ p2) → (p2 → (p2 ∨ (((True ∧ p1) → (p3 ∨ p1)) ∧ True)))) ∧ p5))) ∨ p5) → p5) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110878583951207708891190068882 : (((((((((False ∨ p5) ∨ p3) ∨ p1) ∨ (((False → p2) ∧ p5) → True)) ∨ (False ∨ p2)) ∧ ((True → p1) ∨ p1)) → p5) ∧ p3) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234883791668959067282017445245 : ((p5 → (p4 → p5)) → ((((True ∧ (True → False)) ∨ (p2 ∧ ((p2 ∧ p5) ∨ p3))) ∨ p1) ∨ ((True → (p2 ∧ ((p4 ∨ p5) ∧ False))) → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702401705898915909470739192814 : (((((((p1 ∨ False) ∧ p2) ∨ (p5 ∨ (p4 ∧ p1))) ∨ p4) ∨ ((p3 ∨ True) ∨ (((p5 ∨ p2) → (True → p1)) ∧ (p1 ∧ (p4 ∨ p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263402145973064504163741385245 : (True ∧ (((p4 → (((False → p1) → (p5 ∧ p1)) ∨ p4)) → ((((p2 ∨ p2) ∧ (True ∧ (p2 → p1))) ∨ p2) → p5)) ∨ (True ∨ (False ∧ p3)))) := by
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
theorem thm_5_vars_258278567853982094971170963730 : ((p5 ∨ True) → (((p3 ∨ (p1 → (((p5 ∨ p4) ∨ (p1 ∧ ((p4 ∨ False) → p1))) ∧ (p5 ∧ (False ∨ p1))))) ∨ ((True ∨ p3) ∧ True)) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro



