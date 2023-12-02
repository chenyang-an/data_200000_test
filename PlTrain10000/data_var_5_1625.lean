variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_769912022463368604903701449797 : (((p5 ∧ (True → (p2 ∨ ((p4 ∧ ((p1 ∧ p3) ∧ (False ∨ p2))) ∧ (((p4 → p3) ∨ p2) ∨ (p5 ∧ ((p5 ∨ (p3 ∨ False)) → p4))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312985427644265931720224283868 : (p3 ∨ (((p5 ∨ (((p2 ∧ ((p5 ∨ ((((p2 ∨ True) → p2) → p2) ∧ p1)) ∨ ((False ∧ (True ∧ p1)) → p4))) ∨ p4) ∧ p1)) ∧ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_691658455207085333463065311154 : ((((p5 ∧ (((True ∧ p5) → ((p5 → True) ∧ (p5 ∧ (p5 ∧ (p2 ∨ p5))))) ∨ False)) → (((p3 → (p3 ∧ (p2 ∧ p2))) ∨ p2) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257124356007127629538924932399 : ((p2 ∨ p1) → (((True ∧ (p4 ∨ ((p4 → (True → ((True → (p5 ∧ ((p2 → p1) → (p4 → False)))) ∨ p4))) → p2))) ∨ (p4 ∨ p1)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205820039239753531602562656886 : (((p5 ∨ p1) → (p1 ∧ (False ∧ p5))) ∨ (((p1 ∧ p5) ∨ ((p4 ∨ (((p1 ∧ p4) ∧ (p5 ∨ p5)) → p5)) ∧ (True ∧ p4))) ∨ (False → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313314872054843165833911732316 : (p3 ∨ ((p2 ∨ ((((True ∨ p1) → False) ∧ (((p3 ∧ p3) ∧ ((p4 → p3) → p5)) → ((p4 ∨ (True ∨ (p1 → p5))) → p4))) → p4)) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (True ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620210223391105650335776437372 : (((((p4 ∧ True) ∨ ((p2 → p1) ∧ ((p2 ∨ ((p3 ∧ (p2 ∨ (p2 → p5))) ∨ (False ∨ ((p1 ∨ p2) → False)))) ∧ (p3 ∧ p4)))) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_47552832886025585476832833275 : (((True → (((True ∨ True) ∧ (p4 ∨ (((p4 → ((p2 ∧ (True ∨ True)) ∨ p4)) ∧ (p3 ∨ False)) ∨ p5))) ∨ (True ∧ p1))) ∨ (p3 ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327174063790459216171033270355 : (True → ((False ∨ (((p3 ∨ (p1 ∧ (p2 ∧ (False ∧ (False → (p3 ∨ p3)))))) ∧ p2) ∨ (p4 ∨ (p1 ∨ (p1 → (p5 ∨ (p1 ∨ p1))))))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158425922791492146506554613441 : (((p5 ∧ p2) ∨ (True → ((p2 ∧ p1) ∧ (p1 ∨ ((p2 ∧ p3) ∨ (p3 → (p1 ∨ (p5 → p3)))))))) ∨ (False → ((p5 ∧ p1) → (p4 ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136235371029611482512401096620 : ((((p2 ∧ p1) ∧ ((p4 ∧ True) ∨ p5)) ∨ ((p5 → (True → (p4 → (p2 → p1)))) ∨ (p4 ∧ (p2 ∨ (True ∨ True))))) ∨ (True ∨ (p3 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205455702311591687926939788610 : (((True → (False → p5)) → (p1 ∧ p1)) ∨ (((((p1 ∧ p2) ∧ p1) ∨ p1) → ((p2 ∧ p1) ∨ (p3 → ((True ∨ False) ∨ p3)))) ∨ (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116222143918061410630769855795 : ((((p4 ∨ p2) ∨ p3) ∨ (p3 ∧ (True ∨ (p3 ∨ ((p4 ∨ (((p3 → (False ∨ (p2 ∧ p1))) ∨ p5) ∨ (p4 → True))) ∨ p3))))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147350959784042944466429350891 : (((((p4 → (p1 ∨ (False → (p4 ∧ True)))) ∨ (p5 → (True → (p3 ∧ False)))) ∧ (p1 ∧ (p3 ∧ False))) ∨ p4) ∨ (p4 ∨ ((False ∨ False) → p5))) := by
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
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54099539882129853272399623680 : (((True ∧ (False ∨ ((p5 ∧ ((True ∧ p3) → p2)) ∨ True))) → ((p4 ∨ ((p2 ∨ p3) ∨ (p3 → ((True ∧ (True ∧ False)) → True)))) ∧ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- Implications on the right can always be decomposed.
      intro h10
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- Implications on the right can always be decomposed.
      intro h13
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171658689367691589357505872965 : (((p2 ∧ ((((p4 ∧ (False ∨ p3)) ∧ ((p5 → p2) ∧ False)) ∨ p4) ∨ p4)) ∨ True) ∨ (p2 ∧ (p4 ∨ (p1 → (False ∧ ((p1 ∧ p4) ∨ p2)))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311198382864113554356805814427 : (p2 ∨ ((p3 ∨ p4) → (p3 → (((p1 ∧ (p1 ∧ ((False ∧ ((p4 ∨ ((p3 ∨ p5) ∨ True)) ∧ True)) ∧ p4))) ∨ (p4 → (True ∧ p3))) ∨ p3)))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256403887889994270535111103936 : ((False ∨ p3) → ((p4 ∧ (p3 → ((((False ∧ ((((p5 ∨ p2) → p3) → True) ∧ (p4 ∧ p5))) ∨ ((p2 → p3) ∧ p1)) → p4) ∧ False))) → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h7 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h8 := h4 h7
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157600189357421851654291414449 : (((p2 → (p5 ∧ ((p4 → p3) ∧ ((p2 ∧ p3) ∧ ((p4 ∨ (p3 ∨ p3)) ∧ p5))))) → (p5 ∧ p3)) ∨ (p1 → (p1 ∧ (p1 ∧ (p5 → p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54740460462374718008506716542 : ((((False ∨ (p1 ∧ True)) → ((p5 → p5) ∧ p2)) → ((p4 ∨ (((p3 ∨ True) → p5) ∨ True)) ∨ ((((p1 ∧ p5) ∨ p1) ∧ True) ∧ p3))) ∨ p4) := by
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
theorem thm_5_vars_198458985346481857636891003122 : ((p5 ∧ ((False → p1) ∧ ((p4 ∧ False) ∧ p1))) ∨ ((p5 ∧ p4) ∨ (((((((p3 → p2) ∨ False) ∧ p4) ∨ p4) ∧ (False ∨ p2)) ∧ True) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303799329874893179184072268795 : (p1 ∨ ((((((p2 → (True ∧ ((p4 ∨ p3) ∧ (False ∨ (p5 → p3))))) ∨ (True → p4)) → False) ∨ ((False ∧ (p4 ∨ True)) → False)) → p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42541972428725007950448871148 : (((p1 ∨ (((((p3 ∨ p5) ∧ True) → ((p4 ∨ ((p3 → (False ∨ False)) ∨ p5)) ∧ p1)) → False) → (p5 ∨ (p5 ∨ (p1 → p4))))) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_864760115187203441028269835633 : (((((p4 ∧ (((p1 → p5) ∨ p1) ∧ (False ∨ p4))) → (((p5 ∨ (p5 → p5)) ∧ False) ∨ (p2 ∨ ((False ∧ (p3 ∨ p4)) → p1)))) → False) → False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p4 ∧ (((p1 → p5) ∨ p1) ∧ (False ∨ p4))) → (((p5 ∨ (p5 → p5)) ∧ False) ∨ (p2 ∨ ((False ∧ (p3 ∨ p4)) → p1)))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- False on the left can always be used.
        apply False.elim h9
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- False on the left can always be used.
        apply False.elim h12
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h15 =>
        -- False on the left can always be used.
        apply False.elim h15
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h17
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- False on the left can always be used.
        apply False.elim h18
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h20 := h1 h2
  -- False on the left can always be used.
  apply False.elim h20
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227564653348494320479370043770 : ((True ∧ (p5 → p1)) ∨ ((p3 ∧ (((p4 ∧ ((p5 ∨ (p3 → ((p2 → (p4 ∨ ((p4 ∨ p4) ∧ False))) → p1))) ∧ p2)) ∧ True) ∨ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615501885211984280644716601285 : ((((((p4 → (p5 ∨ ((((True → (p5 ∧ False)) ∧ p5) ∧ p1) ∨ p3))) ∧ (True ∧ True)) → (((False ∨ False) ∨ (p2 → p3)) ∧ False)) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_351292416439591732608618445271 : (p4 → (((((p5 ∨ (p1 ∨ (p2 ∨ (p1 → (False → p1))))) ∧ (p2 ∨ (False → p2))) ∨ (p1 → True)) ∨ (True ∨ p5)) → (p5 ∨ (p4 ∨ p3)))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h8 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h7
        case inr h9 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h7
      case inr h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Disjunctions on the left can always be decomposed.
          cases h6
          case inl h12 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h1
          case inr h13 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h1
        case inr h14 =>
          -- Disjunctions on the left can always be decomposed.
          cases h14
          case inl h15 =>
            -- Disjunctions on the left can always be decomposed.
            cases h6
            case inl h16 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h1
            case inr h17 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h1
          case inr h18 =>
            -- Disjunctions on the left can always be decomposed.
            cases h6
            case inl h19 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h1
            case inr h20 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h1
    case inr h21 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h22 =>
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h23 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h24 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314825268337468229444083323321 : (p3 ∨ ((((p1 ∧ ((((False ∧ False) ∧ p5) ∧ p3) ∨ True)) ∧ False) ∨ False) ∨ (p5 → (((False → (p2 → False)) → False) → (p3 ∨ (p4 ∧ p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (False → (p2 → False)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h3
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191398040347049044405112533791 : (((p1 ∧ True) → ((p3 ∨ p4) ∧ ((p2 ∨ p5) ∧ True))) ∨ (p5 → (((((True ∨ p3) → p1) ∨ ((p4 → (p4 → p1)) ∧ p2)) ∨ True) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783761711478681119216100310711 : (((p3 ∨ (((p3 ∨ (p3 → p3)) → p5) ∧ (True ∧ (((((False ∧ False) ∨ p2) ∧ (p5 → p5)) ∨ ((p1 ∧ p3) → (p1 → False))) ∧ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117094688411794331788452710783 : (((p1 → p3) → (((((((p2 ∧ p5) → (p1 → (p4 ∧ p4))) → p3) → (True ∧ True)) ∨ (False ∧ (True ∨ p3))) → False) ∨ False)) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_811383052393771274122952919848 : (((p5 → (p2 ∨ ((((((p3 ∨ p2) ∧ p4) → (p3 → True)) ∧ (p3 ∧ p4)) ∨ (((p2 → True) ∨ p4) ∨ (p5 ∨ (p1 ∨ p4)))) ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112920821233537158962690301843 : ((((p4 → p2) ∨ ((False ∧ (p1 ∧ (((p2 ∨ False) ∨ (((p5 → False) ∨ p2) ∧ p3)) ∧ p5))) → (p5 ∧ (p3 ∧ True)))) → p5) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136539754706819856927394996716 : ((((False ∧ p1) ∧ p5) ∨ (False ∨ (((p2 ∧ p4) ∧ p4) ∧ (((False ∧ (p5 ∧ p4)) ∨ p3) ∧ ((False ∧ p5) ∧ True))))) ∨ (False → (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110935057077256963439401324266 : ((((((((p5 ∧ p3) ∧ p1) ∨ p5) → ((p1 ∨ (p1 → ((p5 ∨ True) ∧ p3))) ∧ p3)) → (False ∨ p5)) ∧ (True ∧ False)) ∧ p4) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_625257120284677827172224820444 : ((((True → (p3 ∨ (((p1 ∧ (((False → p3) → (((True ∨ p4) ∨ False) ∧ p4)) → p1)) ∨ p2) ∨ ((p5 ∧ p1) ∨ (p4 → p4))))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621367333070474561365050513593 : ((((True ∧ (p1 ∧ (((p1 ∧ p2) ∨ True) → ((((False ∧ p3) → p2) ∧ p5) ∨ ((((True ∧ p1) ∧ p4) ∨ (p3 ∧ p4)) ∧ p2))))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_148620458990815584005151669468 : ((((p2 → ((p5 ∨ p2) ∧ True)) ∨ (True → (p2 → p4))) → (p4 ∨ (p4 ∨ ((p3 ∧ p3) ∧ (False → False))))) ∨ (p4 → (p5 → (p5 ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_715914765577383393003374078960 : (((((p3 ∨ (p1 ∧ p2)) ∨ p3) ∧ (p5 ∧ ((p4 → p3) ∨ ((True ∧ (p4 ∧ (((p4 ∧ (p4 ∨ True)) ∨ p4) → (p1 ∨ True)))) ∧ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_759532242845987074073836071755 : (((p2 ∧ ((p4 → (((p1 → ((p3 ∨ ((p2 → p3) → (False ∨ p2))) ∧ p5)) ∧ p4) ∧ (p4 ∨ p2))) → (p5 ∧ ((True ∧ p3) ∧ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608477941462485466262091378562 : (((((((((True → False) → ((p2 ∧ p3) ∧ (False ∧ ((True ∧ p4) → True)))) ∧ p2) ∧ (False → (p1 ∨ (False ∧ p1)))) → p3) ∨ True) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_48471188782337385968287515628 : (((((((p3 → (False ∧ (False → (p4 ∧ p5)))) ∨ (p1 → p3)) ∧ p3) ∧ (p5 ∧ (p3 ∨ (False → p4)))) ∧ True) ∧ (p3 ∨ (p5 ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_81095515022917755249427010955 : (((((p1 → False) ∧ p3) ∨ (((((((p4 → p2) → True) ∧ p4) ∨ True) ∨ p3) ∨ p2) ∨ (p5 → (False ∧ p5)))) ∧ (p4 ∧ (True → p5))) → p5) := by
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
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h10 := h8 h9
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h14 =>
          -- Disjunctions on the left can always be decomposed.
          cases h14
          case inl h15 =>
            -- Conjunctions on the left can always be decomposed.
            let h16 := h15.left
            let h17 := h15.right
            -- Conjunctions on the left can always be decomposed.
            let h18 := h3.left
            let h19 := h3.right
            -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
            have h20 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h19, we can now drive its conclusion.
            let h21 := h19 h20
            -- One of the premise coincides with the conclusion.
            exact h21
          case inr h22 =>
            -- Conjunctions on the left can always be decomposed.
            let h23 := h3.left
            let h24 := h3.right
            -- We want to use the implication h24 based on <expert-advice>. So we show its premise.
            have h25 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h24, we can now drive its conclusion.
            let h26 := h24 h25
            -- One of the premise coincides with the conclusion.
            exact h26
        case inr h27 =>
          -- Conjunctions on the left can always be decomposed.
          let h28 := h3.left
          let h29 := h3.right
          -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
          have h30 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h29, we can now drive its conclusion.
          let h31 := h29 h30
          -- One of the premise coincides with the conclusion.
          exact h31
      case inr h32 =>
        -- Conjunctions on the left can always be decomposed.
        let h33 := h3.left
        let h34 := h3.right
        -- We want to use the implication h34 based on <expert-advice>. So we show its premise.
        have h35 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h34, we can now drive its conclusion.
        let h36 := h34 h35
        -- One of the premise coincides with the conclusion.
        exact h36
    case inr h37 =>
      -- Conjunctions on the left can always be decomposed.
      let h38 := h3.left
      let h39 := h3.right
      -- We want to use the implication h39 based on <expert-advice>. So we show its premise.
      have h40 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h39, we can now drive its conclusion.
      let h41 := h39 h40
      -- One of the premise coincides with the conclusion.
      exact h41



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_741662850959723441602845008570 : ((((True → False) ∨ (((False ∨ ((p2 ∧ (False → p3)) ∧ ((False ∧ False) ∨ p1))) → (p5 ∨ (p5 ∧ (p2 ∧ p2)))) ∨ ((p4 ∨ False) ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115896683636021067707683833019 : (((((True ∧ p2) ∨ p5) → False) ∨ ((p5 ∧ True) ∨ ((((True ∨ p2) → False) ∧ ((p5 → ((p2 ∨ p4) → p1)) ∨ p1)) → p5))) ∨ (p2 ∨ p4)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : (True ∨ p2) := by
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
    have h8 : (True ∨ p2) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h9 := h2 h8
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_71421844097931557915200573839 : ((((p4 ∧ p1) ∨ ((p1 ∨ (True ∨ p3)) ∧ ((True ∧ ((((p4 ∨ ((p1 ∧ p2) ∨ True)) ∨ p1) → (p4 → p1)) ∨ True)) → p4))) ∧ p3) → p4) := by
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
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h11 : (True ∧ ((((p4 ∨ ((p1 ∧ p2) ∨ True)) ∨ p1) → (p4 → p1)) ∨ True)) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h12 := h9 h11
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
        have h15 : (True ∧ ((((p4 ∨ ((p1 ∧ p2) ∨ True)) ∨ p1) → (p4 → p1)) ∨ True)) := by
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h9, we can now drive its conclusion.
        let h16 := h9 h15
        -- One of the premise coincides with the conclusion.
        exact h16
      case inr h17 =>
        -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
        have h18 : (True ∧ ((((p4 ∨ ((p1 ∧ p2) ∨ True)) ∨ p1) → (p4 → p1)) ∨ True)) := by
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h9, we can now drive its conclusion.
        let h19 := h9 h18
        -- One of the premise coincides with the conclusion.
        exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153147183904824837989938160302 : ((p5 ∧ ((False ∨ (True → ((p4 → (p4 ∨ p1)) ∨ ((((p2 → False) ∧ True) ∨ (True ∧ p5)) ∧ p2)))) ∧ p2)) → ((p4 ∨ (True → False)) ∨ True)) := by
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
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165830542319987853900811564485 : (((p3 → (p1 ∨ False)) ∧ (False ∨ ((((True ∨ (False → p5)) ∧ p1) → p3) ∧ (True ∧ True)))) ∨ (((False → p5) ∧ ((False ∧ p2) → p3)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167102631992197601235859503628 : ((((p5 → (((((p3 ∨ False) ∨ False) ∧ p5) ∨ False) → (p1 ∧ p2))) ∨ (True → False)) ∨ p5) → ((True → p5) → (((p4 ∨ p3) ∨ p1) ∨ True))) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
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
theorem thm_5_vars_256781893765249121175952287548 : ((p1 ∨ p2) → (((p3 ∨ p3) → (p3 ∧ ((p2 ∧ p1) ∨ ((False → p2) ∨ True)))) ∧ (((p3 → (p5 ∨ p3)) → (False ∨ True)) ∨ (False ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h4 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h5 =>
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h6
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h15 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h16
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h17 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h18
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307709557866438608364624340070 : (p1 ∨ (p2 → (False ∨ (((p2 → ((False → (((p1 ∨ (p5 → p3)) → (False ∧ (p2 ∧ p1))) → p4)) → (p4 ∧ (p5 ∧ True)))) ∨ False) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114676280720505291069542758326 : (((p3 ∧ ((False ∧ (((False ∨ p5) → ((True ∨ p2) ∧ (False → p3))) → True)) ∧ p5)) ∨ (((p5 ∧ (p5 ∨ False)) ∨ True) ∨ p5)) ∨ (p3 ∨ p2)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_586089417164370005954927231757 : (((((((p1 ∧ (((((p1 → p2) → False) → (p2 → (p5 ∧ False))) → p3) ∧ True)) ∨ p4) ∨ ((p5 ∧ (p4 → p1)) ∨ False)) ∧ p3) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180540653845343867711618816911 : ((((p2 → p1) ∨ ((p5 ∨ (p5 → p2)) ∧ True)) ∨ ((p1 ∧ False) ∨ p2)) → ((True → ((((True ∨ (p4 ∨ p4)) ∧ p4) ∨ p2) → p4)) ∨ True)) := by
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
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159910485902890166096275381115 : ((((False → (((p1 ∨ p4) → (p4 → p5)) → (((p4 ∨ p4) ∧ (p2 → False)) ∨ p4))) ∨ p2) → p2) → (((p2 ∨ (True → False)) ∧ p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184980273111924171046761344003 : (((p1 → (p2 ∨ False)) → ((((p5 ∧ p5) → False) → p2) ∧ p3)) ∨ (p4 ∨ (True ∨ ((p2 ∧ (((False → p4) ∨ (True → p1)) ∧ p2)) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_94212048671104659023714248027 : ((p2 ∧ (((p4 ∧ ((p4 → p5) ∧ ((False ∧ False) ∧ (((p5 ∧ p5) ∧ p4) ∨ (p5 → False))))) ∨ ((True ∧ p1) ∨ (p3 → p2))) → False)) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((p4 ∧ ((p4 → p5) ∧ ((False ∧ False) ∧ (((p5 ∧ p5) ∧ p4) ∨ (p5 → False))))) ∨ ((True ∧ p1) ∨ (p3 → p2))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_675294458286661404411699532116 : (((((((((p4 ∧ p4) → p2) ∨ ((False ∨ (True ∨ (p5 ∨ p2))) ∨ (p1 ∨ p4))) ∨ p4) ∧ p4) → False) ∧ (True ∧ (p4 → (p4 ∨ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_710103502631996398930669019775 : (((((((p1 → False) ∧ p5) ∧ False) ∨ True) ∧ ((True ∨ p3) → ((((p4 → (p2 → (((p5 ∨ p5) ∧ p1) ∨ p2))) ∧ True) → p2) ∨ True))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338406860220523808182043750274 : (p1 → (((p2 → (p1 ∧ p2)) → p2) → (p4 ∨ ((p3 ∨ (((False ∨ p2) ∨ p4) ∨ (False ∧ p1))) ∨ (p1 → (p1 → ((True ∧ p3) ∧ False))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p2 → (p1 ∧ p2)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h1
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68028256637589372872805626485 : ((p2 → (p1 ∧ ((((False ∧ False) ∨ p3) ∧ p4) ∧ (((False ∨ p5) ∧ p1) ∧ (False → ((p2 ∧ ((p2 → p4) → (p3 → False))) → p1)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56581204086718931985376407494 : (((p1 → ((p2 → True) ∧ p1)) → (p5 ∨ (((False → (False → p4)) ∨ ((p5 ∨ p2) ∨ ((p3 → p1) ∨ p3))) ∧ (p5 ∨ (p4 → p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_595671640833009493535834352854 : (((((True ∨ (True ∨ (p5 ∧ ((p2 ∧ ((p2 → p5) ∧ p2)) → p2)))) → (((((False ∧ False) ∧ p4) ∧ p5) ∨ (p3 ∨ p2)) → p5)) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52621640731334547223031128329 : ((((False ∨ (p4 ∧ False)) ∨ ((False ∨ p1) ∨ (p3 → ((False → True) ∨ p1)))) ∨ ((True ∧ p3) → (((p5 ∧ True) → False) ∧ (False ∧ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157747519599344393561319172871 : ((((p5 → (p1 → ((((p1 ∧ False) ∧ p3) → True) ∧ False))) → p1) ∧ (True ∧ ((p2 ∧ p1) ∨ p1))) ∨ (((p2 → (p4 ∧ p1)) → True) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259759366099287415315127248137 : ((p1 → p2) → ((True ∧ ((((p1 → p4) ∨ (p1 ∧ p1)) ∨ p5) → p3)) ∨ ((p2 ∧ p3) → ((((False ∧ (p2 ∨ p4)) → False) ∧ False) → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_623896861190411576342237337010 : ((((p1 ∨ (p1 → (((p3 → p2) → (p2 ∨ ((False ∨ (p4 → ((((False ∧ (True → p1)) → p5) ∨ False) ∧ p3))) → p5))) ∨ p2))) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260850233204268156058203317322 : ((p4 → True) → (((p2 → (True → ((True ∧ (False ∨ p2)) ∨ p5))) ∨ (True ∨ (p3 ∨ p4))) → ((True → p3) → ((p4 ∧ (p4 ∧ p1)) → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h9 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h10 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h11 := h3 h10
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h14 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h15 := h3 h14
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- One of the premise coincides with the conclusion.
        exact h17
      case inr h18 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h19 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h20 := h3 h19
        -- One of the premise coincides with the conclusion.
        exact h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111643925257206779927899695572 : (((((p2 ∧ ((False → p2) → p2)) ∨ (p5 ∨ ((p2 ∧ (True ∧ p5)) ∧ (p5 ∧ ((True ∧ p2) ∨ (p4 ∨ p1)))))) ∨ p5) ∨ True) ∨ (p2 ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175207294960531633366654865688 : ((False ∨ ((p1 ∨ p5) → ((p3 ∨ ((False ∨ p3) → (p1 ∧ p4))) ∨ (p5 → True)))) → (((p3 → (True → False)) ∧ (p2 ∧ (p5 ∧ p3))) → False)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h11 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h12 := h3 h11
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h13 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h14 := h12 h13
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159688140169370469947613804530 : (((((p1 → p1) ∧ (((True ∧ (p4 → (p2 ∧ p5))) ∨ True) ∨ (True ∨ p5))) ∨ (False → p5)) ∨ p5) → ((((p2 ∧ p5) ∨ p4) ∨ p1) ∨ True)) := by
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
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h13 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313335511988707521059674223511 : (p3 ∨ ((p5 ∨ (True → ((p2 → (((False ∧ (p4 → (p2 ∧ (p4 ∨ p2)))) ∨ p5) ∧ p3)) ∨ (((True → (p2 ∧ p4)) → p4) ∨ p1)))) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_804145901453469632206937177635 : (((p3 → ((((p4 → (p2 ∨ p2)) ∧ ((True ∨ p3) ∧ (((p4 → p4) ∨ False) ∨ (False → p2)))) → p2) → (((p1 ∨ p1) → p4) ∨ p3))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43753466595561284719399520383 : ((((False ∧ (p4 ∧ (((p3 ∨ p5) → p5) ∨ (p3 → (((p1 → (p4 ∧ (p2 → (p1 ∨ p3)))) → p1) ∧ (p5 ∧ p3)))))) → p5) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_240875010258613047009730155599 : ((True → True) ∧ (((((True ∧ p1) → p5) ∨ p5) → p3) ∨ ((p2 ∨ p1) ∨ (False → (p4 → (p5 → ((False ∨ p3) → (True → (p3 ∨ p4))))))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_793198279899459070370327561849 : (((True → (False ∧ ((p3 ∨ p2) ∧ (((((p4 ∨ ((p2 → p3) → p5)) ∧ (p3 → p1)) ∧ p2) ∨ False) ∧ ((p2 → p1) ∨ (False ∧ p2)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683360908060175568869637670924 : ((((p5 ∨ (((p2 → ((((p2 ∧ p3) ∧ p1) → p1) → (True → True))) ∨ False) ∨ (p3 ∨ p2))) ∧ ((p2 ∧ (p1 → p1)) → (p4 ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149633771512052296032968815372 : ((p4 ∧ ((p3 → (((True ∧ ((False ∧ True) ∨ (p5 ∨ p2))) ∨ (((True → False) ∧ p1) ∨ p2)) → p5)) ∨ p1)) ∨ (p4 ∨ (p2 → (True ∧ p2)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_458478147522973937011515461368 : ((((p5 ∧ ((((True ∨ (p5 ∧ True)) ∧ ((p1 ∨ p2) ∧ ((p1 → p1) ∧ p5))) ∧ p5) ∧ True)) ∨ (((p2 ∨ p1) ∧ (p2 ∧ p5)) → True)) ∧ True) ∧ True) := by
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
theorem thm_5_vars_351256252620704830410116500036 : (p4 → ((p3 ∧ (((((p1 ∨ p5) ∧ (((False ∧ (False → p4)) → p1) ∨ (p3 → p2))) → (True ∨ p4)) → p3) ∧ p5)) ∨ ((p5 ∨ True) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308544085975905222443049448212 : (p2 ∨ ((((p2 ∧ ((p3 ∨ p2) ∧ p4)) ∧ ((p1 → False) ∨ p5)) ∨ ((False ∨ ((p5 ∨ p2) ∧ ((p2 → (p1 → True)) ∧ p4))) ∨ True)) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608745846299373596128277682034 : (((((((p5 → ((((p3 → False) → (p3 → p5)) ∧ p4) → (p2 ∧ (True → False)))) ∧ (p1 → True)) ∧ (p4 ∧ (p3 ∨ False))) ∨ p5) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_686221243936064965266450066090 : ((((((p5 → ((p2 ∧ (p2 ∨ p5)) ∨ (p4 → p3))) → p4) → ((p4 ∧ (p5 → p2)) ∨ False)) → (True ∧ ((False ∨ p4) ∨ (p4 ∨ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54238170503627251349983319370 : ((((p2 → (True ∨ (True ∨ (False → False)))) → p2) ∧ ((p5 → ((p3 → p4) ∨ ((((p4 ∨ p1) → True) ∧ p4) ∧ p4))) ∨ (p4 ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_586797165265377511357037676404 : (((((p3 ∧ (p5 ∧ (((((p1 ∨ p3) ∨ ((p3 ∧ (True ∧ True)) ∧ p4)) ∧ p4) → p5) → ((p2 ∧ p4) ∧ (p1 → p2))))) ∧ p3) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_592595813482417233115392494407 : (((((True ∨ (p3 ∨ (((p3 ∨ (False → (p1 ∧ False))) ∨ (p4 ∨ (p2 → ((p1 ∨ (p1 ∧ False)) → p3)))) → False))) → (p3 ∨ p5)) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179541420224751673323586091898 : ((p1 → ((False ∨ ((p1 → p4) ∨ False)) → ((p4 ∧ p5) ∨ (True ∧ False)))) ∨ ((False ∨ (p1 ∨ (False → p1))) ∨ (p1 ∨ ((False ∧ p3) → p2)))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328496793567413863037237756340 : (True → (((p5 ∧ p1) → (p1 ∧ ((p5 → (((p1 ∧ p4) ∨ (p3 ∨ False)) ∧ False)) ∨ True))) ∧ ((p1 → ((p5 ∧ True) → (p2 ∨ True))) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_874508936795672422491178875874 : ((((((True → ((((((p1 ∨ (p4 → p1)) → (p1 ∧ True)) → p2) → p1) ∧ p4) → p2)) ∧ ((False → p4) ∧ p2)) ∧ p5) ∧ (p4 → p1)) → p2) ∧ True) := by
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
  let h8 := h7.left
  let h9 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49794185531179524407679756469 : (((p5 ∨ ((((p2 → p4) ∧ p1) → ((p1 ∧ ((p2 ∧ p1) ∨ (p3 ∧ False))) ∨ p2)) ∧ (p4 → (p4 ∧ False)))) → ((True → p4) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_18756236311377720694765753324 : ((((((p5 ∨ p3) ∧ (((True ∧ (p1 ∨ (p3 ∧ p5))) → p3) ∨ p4)) ∧ (p2 → p4)) ∨ p5) ∨ (((p5 ∧ p4) ∨ p1) ∨ (True ∨ p4))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114653505104750035477813047165 : ((((p5 ∧ (p2 ∧ (p5 ∨ ((p4 ∧ p5) ∨ p2)))) ∨ (False → (False ∧ (False ∧ p2)))) ∨ (p4 ∨ (((p5 → True) ∨ p4) ∨ True))) ∨ (p2 → p2)) := by
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
theorem thm_5_vars_50274467738558500811635518214 : (((((((p5 ∨ (True ∧ p4)) ∨ (False → p3)) ∨ (False ∨ (p3 ∨ p1))) → (p5 ∧ p4)) ∨ (p1 → False)) ∨ (True ∨ ((p3 ∧ False) → p3))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_195708387967480077264154293980 : (((True ∨ p5) ∨ ((p5 → p4) ∧ (p4 ∨ p4))) ∧ (p2 ∨ ((False ∨ ((False ∧ p1) ∨ ((p5 ∧ (((p5 ∧ p3) ∨ p5) → p2)) ∨ p2))) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354051927938144383390600581168 : (p4 → (p4 → ((False ∧ p1) ∨ ((p4 ∨ ((p3 ∨ p3) ∨ True)) ∧ (False ∨ ((p3 ∧ (p1 ∨ (p5 ∨ p2))) ∨ (p2 → (p4 ∨ (p1 ∧ p2))))))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302569883771890429575876208484 : (False ∨ (p1 ∨ ((True ∧ (((p3 ∨ False) ∨ False) ∨ ((False → (p2 ∧ (p4 ∨ True))) ∨ (False ∧ (p2 ∨ ((p3 → p5) ∧ p1)))))) ∨ (True → p4)))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227514275159482007961490604590 : ((True ∧ (p3 ∨ p1)) ∨ (((True ∨ p3) ∧ (((p3 ∧ p3) ∧ (p4 ∨ p3)) ∧ (p5 ∧ (False ∨ p3)))) ∨ (p3 → (p1 → (p2 → (p2 ∨ p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139848887230760575554630689282 : (((p4 → ((((p3 ∧ (False → p1)) ∨ True) ∧ (False ∨ False)) ∨ ((p1 → (p4 ∧ (p3 ∨ p1))) ∧ (p4 ∨ p1)))) → p4) → ((p3 ∨ True) ∧ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p4 → ((((p3 ∧ (False → p1)) ∨ True) ∧ (False ∨ False)) ∨ ((p1 → (p4 ∧ (p3 ∨ p1))) ∧ (p4 ∨ p1)))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135996542112597194372548153469 : ((((p1 → p5) → (((p5 → (p4 ∨ p3)) ∧ p5) → p3)) ∨ ((p5 ∧ p4) ∧ (p5 → (((p5 → p3) ∨ p5) ∨ p2)))) ∨ ((True ∨ False) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338174127831212849293084674023 : (p1 → ((p2 ∧ ((False ∨ (False ∨ True)) ∨ (p2 → False))) → ((False ∧ ((False ∧ False) ∧ False)) ∨ ((p5 ∧ p3) ∨ ((True ∨ True) → (True → p1)))))) := by
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
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- False on the left can always be used.
        apply False.elim h8
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h10
        -- Implications on the right can always be decomposed.
        intro h11
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h12 =>
          -- One of the premise coincides with the conclusion.
          exact h1
        case inr h13 =>
          -- One of the premise coincides with the conclusion.
          exact h1
  case inr h14 =>
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h15 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h16 := h14 h15
    -- False on the left can always be used.
    apply False.elim h16



