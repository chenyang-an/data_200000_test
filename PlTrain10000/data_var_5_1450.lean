variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151301498451628372084293891770 : (((p1 ∨ ((p2 ∧ ((p1 → (True ∨ p1)) ∧ ((p3 ∧ (p5 ∧ (p3 ∨ (False ∨ p1)))) ∨ p5))) → p2)) → False) → (((p4 ∨ p4) ∨ p5) ∧ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 ∨ ((p2 ∧ ((p1 → (True ∨ p1)) ∧ ((p3 ∧ (p5 ∧ (p3 ∨ (False ∨ p1)))) ∨ p5))) → p2)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- False on the left can always be used.
          apply False.elim h15
        case inr h16 =>
          -- One of the premise coincides with the conclusion.
          exact h4
    case inr h17 =>
      -- One of the premise coincides with the conclusion.
      exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h18 := h1 h2
  -- False on the left can always be used.
  apply False.elim h18
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h19 : (p1 ∨ ((p2 ∧ ((p1 → (True ∨ p1)) ∧ ((p3 ∧ (p5 ∧ (p3 ∨ (False ∨ p1)))) ∨ p5))) → p2)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h20
    -- Conjunctions on the left can always be decomposed.
    let h21 := h20.left
    let h22 := h20.right
    -- Conjunctions on the left can always be decomposed.
    let h23 := h22.left
    let h24 := h22.right
    -- Disjunctions on the left can always be decomposed.
    cases h24
    case inl h25 =>
      -- Conjunctions on the left can always be decomposed.
      let h26 := h25.left
      let h27 := h25.right
      -- Conjunctions on the left can always be decomposed.
      let h28 := h27.left
      let h29 := h27.right
      -- Disjunctions on the left can always be decomposed.
      cases h29
      case inl h30 =>
        -- One of the premise coincides with the conclusion.
        exact h21
      case inr h31 =>
        -- Disjunctions on the left can always be decomposed.
        cases h31
        case inl h32 =>
          -- False on the left can always be used.
          apply False.elim h32
        case inr h33 =>
          -- One of the premise coincides with the conclusion.
          exact h21
    case inr h34 =>
      -- One of the premise coincides with the conclusion.
      exact h21
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h35 := h1 h19
  -- False on the left can always be used.
  apply False.elim h35



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_243402442450376553166010780326 : ((p5 → True) ∧ ((p2 ∨ (((((p5 ∨ True) → ((((p4 ∨ p4) ∨ p5) ∨ (True → True)) → p5)) → p1) ∧ True) ∧ ((p5 → p2) ∧ False))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205552121200712395000730580224 : (((p4 ∨ p1) ∧ ((p4 → p5) → False)) ∨ (((p5 → (p4 → ((p4 → ((p1 ∨ ((p4 → (p2 ∨ p5)) ∨ p3)) → p1)) ∧ p5))) ∧ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55056212371925330427866896234 : (((p1 ∨ ((p1 ∨ p3) → (p5 ∧ False))) ∧ ((False ∧ p4) ∧ ((p5 → (p1 ∧ ((p5 → (p2 ∨ p2)) → ((p4 ∨ p1) ∧ p4)))) ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608094344558280013414787348815 : (((((((p3 → (p1 → (((p1 ∨ p4) ∧ ((((False → (p4 → p4)) ∧ p2) → False) ∧ p2)) → (p5 ∧ p5)))) → p1) ∧ p4) ∨ p4) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177717072515740260940784098220 : (((((p4 → (p4 ∨ (p4 → False))) ∧ p1) → (True → (False ∧ True))) ∧ False) ∨ (((p4 ∨ (p1 → p2)) ∧ True) → (True ∨ ((False → False) ∧ True)))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41703166926995874487772439120 : (((((p3 ∨ p3) ∧ ((True → p2) ∨ False)) → ((p2 → ((True ∧ (p5 → ((False ∨ (p1 ∧ False)) ∨ p2))) ∨ p3)) → (p1 ∧ p2))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48908983007344645737494399758 : (((p4 → (p5 ∨ ((p3 ∧ (p2 ∧ (p2 ∨ ((p3 ∧ p1) ∨ ((p1 ∨ p1) → ((p1 ∨ p3) ∧ p4)))))) ∨ False))) ∧ (p3 ∨ (False ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_90919886383792096662438802547 : (((True → False) ∧ (((True ∨ True) ∨ (((p5 → False) → ((p1 ∨ p5) → False)) → (((p3 → True) → (True ∨ p1)) → p2))) ∧ (p2 → p5))) → p4) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h8 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h9 := h2 h8
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h11 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h12 := h2 h11
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h14 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h15 := h2 h14
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310402048000795094693641771010 : (p2 ∨ ((True ∧ (p3 ∨ (p3 ∧ ((p5 → p5) → p2)))) ∨ ((p1 → (((True ∧ True) → p3) ∨ ((p5 ∧ False) ∧ (True ∧ p3)))) → (p4 → True)))) := by
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
theorem thm_5_vars_111850193380304512928761171254 : ((((((((p1 → False) ∧ (True ∨ p3)) ∨ p5) → p2) ∨ (p2 → ((False ∨ (p3 ∧ False)) → False))) → (True → (p4 ∧ p3))) ∨ p3) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729368011038646275235498470163 : (((((p3 ∧ True) ∨ False) → (((((p4 ∨ True) ∧ (((p1 ∨ p2) → p4) ∧ ((((p1 ∨ p1) ∨ p1) → p3) ∨ p5))) → p4) ∨ p3) ∧ True)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201938659707211556325652125424 : (((p1 ∨ (p4 ∨ (True ∨ True))) ∨ True) ∧ (((p2 ∨ (((False ∨ True) ∨ (p3 ∧ p3)) ∨ False)) → False) → ((p4 ∧ p5) ∧ ((p5 ∧ p2) ∨ p5)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 ∨ (((False ∨ True) ∨ (p3 ∧ p3)) ∨ False)) := by
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : (p2 ∨ (((False ∨ True) ∨ (p3 ∧ p3)) ∨ False)) := by
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : (p2 ∨ (((False ∨ True) ∨ (p3 ∧ p3)) ∨ False)) := by
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h6
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306237623982440623740766564546 : (p1 ∨ (((p2 → p2) → p2) → (False ∨ ((p1 ∨ p2) ∨ (((p4 ∨ p2) → (True → (p1 ∧ p2))) → ((p3 ∨ p1) ∧ (True → (p3 ∧ p4)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 → p2) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66565449697998393387177744660 : ((True → (((((p5 → p1) ∨ p4) ∨ ((p5 → (p3 ∧ (True ∧ False))) → (True → False))) → (False ∧ (True ∨ (p4 ∨ False)))) ∨ (False → p2))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305592448363020721233235024582 : (p1 ∨ (((p3 ∧ (p3 ∧ p2)) ∨ (((p1 → (p5 ∨ True)) ∨ p2) → p4)) ∨ ((p4 ∨ (((((p1 ∧ False) ∧ p3) ∧ p1) ∧ p3) ∧ p1)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_70142531643908831515282306190 : (((((False ∧ True) ∨ (((((p3 ∧ (p4 ∨ p5)) ∨ (p3 ∧ False)) → ((p2 ∧ p5) → p3)) → p2) ∨ (True ∨ (p5 ∧ p4)))) → p2) ∧ p1) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((False ∧ True) ∨ (((((p3 ∧ (p4 ∨ p5)) ∨ (p3 ∧ False)) → ((p2 ∧ p5) → p3)) → p2) ∨ (True ∨ (p5 ∧ p4)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166165300602226769873513452178 : ((False ∧ ((False ∧ (p4 ∧ p5)) ∨ ((True ∨ p5) ∧ ((True ∨ (p4 ∨ (p5 ∧ p3))) → p2)))) ∨ ((p4 → p4) ∧ (p2 ∨ ((p4 ∨ False) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316997108348474180021122393413 : (p3 ∨ (p3 → ((p1 ∧ ((p2 → (p1 ∨ p4)) ∧ (p2 ∧ (p3 ∨ p3)))) ∨ (False → (((p1 → p3) → ((p2 ∧ p5) ∨ (p3 → p4))) → p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198252479905044825226212306560 : ((False ∧ (((p3 ∧ (p5 ∨ False)) ∧ p2) ∧ p5)) ∨ (((((True ∨ (p2 → True)) ∨ (p4 → True)) ∧ (p5 ∧ (p1 → (p5 → p4)))) → True) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164853768658625767100332281910 : (((False ∨ (((p4 ∨ (True ∨ (p3 → True))) ∧ ((True ∨ (True ∨ p2)) → p4)) ∧ True)) ∨ p5) ∨ (((p2 ∨ ((False ∧ p5) → p4)) ∨ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164788100842437228873279675858 : ((((p1 ∧ (p2 → (p1 ∧ p1))) ∧ (p5 → (((p1 → True) → p2) → (p5 → p2)))) ∨ False) ∨ ((p1 → p2) ∨ (p3 → (True ∧ (p5 ∨ p3))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158523881548414059430601440789 : (((p4 ∨ p4) → (((p1 ∧ (((True → (False ∧ True)) → p3) → p2)) ∨ (p3 → (p3 ∧ p3))) ∧ p4)) ∨ (True → ((p2 ∨ (p3 → p1)) → False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h3
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h5
    -- One of the premise coincides with the conclusion.
    exact h5
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_665871712871695208418774346854 : ((((((True → (p1 → ((p3 ∨ ((True → p2) ∨ (p1 ∧ True))) ∧ (True → False)))) → (p1 ∨ (p3 ∨ p5))) → p5) ∧ ((True ∧ p5) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_636086082840506633268298559586 : (((((p1 → (((p2 ∨ (False ∨ (p1 → (True → (p3 ∨ p2))))) → (True ∧ True)) ∧ p2)) ∧ ((p3 ∧ (p2 → False)) ∨ (p4 ∨ p1))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345381710417607827117732322072 : (p3 → (((p3 ∧ ((True ∧ (p4 ∨ False)) ∨ (p4 → (p3 ∧ (p1 ∧ ((((False ∨ True) ∧ True) → p4) → (p1 → (False ∧ True)))))))) ∨ p3) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42652309233316448956864789740 : (((p4 ∨ ((((((False ∨ True) ∨ p2) → p3) → (p5 ∧ (False ∨ p5))) ∨ (p4 ∧ (((p5 ∨ (p1 → p1)) ∧ True) ∨ p1))) → p2)) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_639232256161904864263440240507 : (((((p5 → ((True ∧ p2) ∨ p2)) ∨ (((((((p1 ∨ p5) ∨ p3) ∨ p1) ∧ (((p1 ∨ p2) → p3) → p5)) ∨ True) ∧ p5) → p3)) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192972319608558856467068590619 : (((True → ((p3 ∨ (p2 → p4)) ∨ p2)) ∨ (p5 ∨ p3)) → (((((p3 ∧ p4) → False) → p1) ∨ ((p4 ∨ ((p4 ∨ True) ∧ False)) ∨ True)) ∨ p2)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113138648581089046691202762096 : (((p2 → ((p4 ∧ p1) ∧ (((p2 → p3) → ((((p5 ∨ p5) → (p3 ∨ p1)) ∨ (p4 ∨ (p1 ∨ False))) ∧ True)) ∨ p4))) → p1) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64922011760583282776580781420 : ((p2 ∨ ((((True ∧ (p5 → (p4 → p5))) → (p2 ∨ (((p5 ∧ p4) → p2) ∧ True))) ∨ p2) → ((p5 ∨ (p4 ∧ p2)) ∧ (p5 ∨ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123980178162041526841275403248 : (((((((p1 → (p5 ∧ p3)) → p4) → p2) ∧ True) ∧ (p1 → p4)) ∨ (False ∨ ((p4 ∨ ((False ∧ p1) ∧ (p2 ∨ p3))) → p3))) → (p2 → p2)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67457688832645491849966371170 : ((p1 → ((((p1 ∧ ((False → p2) → (((p5 ∨ False) → p1) ∨ p5))) → p3) ∧ (p5 ∨ (p1 → False))) ∨ (p2 → (False ∨ (p1 → True))))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136377762556191126056653879053 : ((((True ∧ p5) ∧ (p5 ∨ p2)) ∨ ((p2 ∧ (((p1 → False) ∨ p2) ∧ (p3 ∧ True))) ∨ (p2 ∨ (False ∨ (p5 ∨ False))))) ∨ (True → (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_762944134433111982773700167120 : (((p3 ∧ ((p1 ∨ ((True ∨ p5) → p2)) ∧ (((True ∨ p4) ∨ (True ∨ True)) ∧ (((p3 ∨ p5) ∧ p3) ∧ (p4 ∨ ((p1 ∧ p2) ∨ p4)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305981475804359594546823544028 : (p1 ∨ ((((False → p4) ∧ p1) ∧ p4) ∨ (p4 ∨ (((((True ∨ p4) ∨ (True ∧ p3)) → ((p1 ∧ True) → False)) ∧ (p4 → (p1 ∨ p3))) ∨ True)))) := by
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
theorem thm_5_vars_120911110089260262135606980486 : ((((((p3 ∨ p4) → p5) → (p2 → p3)) → (((p1 ∧ p1) ∨ p2) → (p5 ∧ (p3 → (((p5 ∨ p1) → p3) ∨ p4))))) ∨ p4) → (p5 ∨ True)) := by
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
theorem thm_5_vars_263400243785693442507201360334 : (True ∧ (((p2 ∧ ((p2 ∨ ((p4 → True) → p4)) ∨ (p3 ∧ p4))) → ((p5 → p3) ∨ (True → (p3 ∨ (True ∨ p5))))) ∨ (p5 → (p1 → p4)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h12
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134939865336874686101720673213 : ((((((p3 ∨ p4) ∨ ((False ∧ p5) ∧ (True ∧ (((p4 ∧ p3) ∨ p1) ∨ p3)))) ∧ p3) ∨ (p1 ∧ p1)) ∧ (p5 → False)) ∨ (True ∨ (p1 ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328444591442240041402643599058 : (True → ((((((p1 ∧ p3) ∨ p5) → (p1 ∨ ((p1 → p2) ∧ (False ∧ (p2 ∧ p3))))) ∧ p1) → p1) → (((p3 ∨ (p1 ∧ True)) → p4) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249490088270220537520887325150 : ((p5 ∨ p1) ∨ ((((((p5 → (p4 ∨ (p4 → True))) ∨ p2) → p5) → (p4 ∨ (p5 → p4))) → (True → p1)) ∨ (False → (p4 ∧ (p2 → False))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186338606765232883013296575710 : ((((True ∧ ((p4 ∧ p2) → p1)) → (p1 ∨ (True → True))) → p3) → ((((True → (p2 → True)) ∧ p3) ∧ (p1 → p3)) ∨ ((p3 ∧ p1) ∧ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : ((True ∧ ((p4 ∧ p2) → p1)) → (p1 ∨ (True → True))) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h4
  -- One of the premise coincides with the conclusion.
  exact h9
  -- Implications on the right can always be decomposed.
  intro h10
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h11 : ((True ∧ ((p4 ∧ p2) → p1)) → (p1 ∨ (True → True))) := by
    -- Implications on the right can always be decomposed.
    intro h12
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h15
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h16 := h1 h11
  -- One of the premise coincides with the conclusion.
  exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313942702947723009876020609420 : (p3 ∨ ((((((p5 ∧ ((((p5 ∨ ((True ∨ (p1 → (p4 ∨ False))) ∧ True)) ∧ p2) ∧ p5) ∨ p2)) → p3) ∧ False) → True) → p4) ∨ (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40890141557751685642228140341 : (((((False ∧ (((p2 ∨ True) ∧ p5) → p3)) ∨ (((((True ∧ p3) ∧ False) → ((p4 ∨ p3) ∧ False)) ∧ False) ∨ p2)) ∧ (p5 ∨ p1)) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308396301374409205614210827089 : (p2 ∨ (((p1 ∧ ((p1 ∨ p2) ∧ ((((p5 ∨ True) → ((p5 → (p5 ∨ p1)) ∨ False)) → (p5 ∧ (True ∧ (False ∨ p4)))) ∨ p2))) ∨ True) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136841672594733599439444709629 : (((p2 ∧ p3) ∨ (((((p4 ∨ p3) ∨ True) ∨ (True ∧ ((p5 → (p4 ∧ p1)) ∧ (p1 ∨ (True → p1))))) → p4) → False)) ∨ (p4 → (p3 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165952007187491607102609360890 : (((p4 ∨ False) ∧ ((((p5 → ((p4 ∧ p4) ∨ False)) → p1) ∨ p3) ∨ (p3 → (p2 → p2)))) ∨ (((p5 ∧ p5) ∨ True) ∨ ((False → p3) ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117872495018729147009650298311 : ((p5 ∧ ((p3 ∨ (True ∧ (p4 ∨ (((p1 ∨ (((False ∨ p4) ∧ (p4 ∧ False)) ∨ (p5 ∨ (p3 ∨ p5)))) → p1) → p4)))) ∨ p5)) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_686641263261415807211194716584 : (((((p1 ∧ p1) → (p4 ∧ (((p3 → p3) → ((p1 ∨ (p1 ∨ (p4 → p4))) → p1)) ∨ p2))) → ((True → p4) ∨ ((p4 ∨ True) ∨ p4))) ∨ p4) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308428105695758553400584129726 : (p2 ∨ ((((((p4 ∨ p2) ∨ p2) ∧ p2) ∧ (True → ((p1 ∧ True) ∧ ((True ∧ (False ∨ (p3 ∧ p2))) ∧ (p5 ∧ (p2 → p4)))))) → p4) ∨ p4)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h9 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h10 := h3 h9
      -- We need to get the right conjuct of h10 based on <expert-advice>.
      let h11 := h10.right
      -- We need to get the right conjuct of h11 based on <expert-advice>.
      let h12 := h11.right
      -- We need to get the right conjuct of h12 based on <expert-advice>.
      let h13 := h12.right
      -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
      have h14 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h13, we can now drive its conclusion.
      let h15 := h13 h14
      -- One of the premise coincides with the conclusion.
      exact h15
  case inr h16 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h17 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h18 := h3 h17
    -- We need to get the right conjuct of h18 based on <expert-advice>.
    let h19 := h18.right
    -- We need to get the right conjuct of h19 based on <expert-advice>.
    let h20 := h19.right
    -- We need to get the right conjuct of h20 based on <expert-advice>.
    let h21 := h20.right
    -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
    have h22 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h21, we can now drive its conclusion.
    let h23 := h21 h22
    -- One of the premise coincides with the conclusion.
    exact h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47811561093189582210868374658 : (((((((False ∨ (p3 ∨ p2)) ∧ ((False ∨ False) → ((p4 ∨ p3) ∧ p5))) → (p4 ∨ True)) → (p5 ∧ (p1 ∧ False))) → p4) → (p5 ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41446526541573412308565569654 : ((((p5 → (p1 → (False → (((p5 ∨ False) ∧ ((p2 ∧ p2) ∨ False)) → p1)))) → (p2 ∧ ((False → True) → ((p2 → p3) → p1)))) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119331634987010936592369895054 : ((p3 → ((((p1 ∨ p2) → p3) ∧ (True → (True ∧ p1))) → (p4 ∨ (p3 ∧ (p4 ∨ (p5 → (((True ∧ False) ∨ p4) ∨ False))))))) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305311363909221707207933438645 : (p1 ∨ ((True ∧ ((((False ∨ p1) → p4) → (p2 ∨ p1)) ∧ ((p4 → True) ∨ ((False ∧ True) → p2)))) ∨ ((True ∧ (False ∧ (p5 ∧ p2))) → p3))) := by
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114449509096261874088703818120 : (((((((((True → p3) → (((p5 ∧ p2) ∨ False) ∧ p1)) ∧ False) ∨ p2) → p2) ∧ p5) ∧ True) → (p3 ∨ (True ∨ (p1 → p5)))) ∨ (p3 ∧ p3)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55794448787120098123165506238 : ((((p3 ∨ True) ∨ (p4 ∧ True)) ∧ (((((p4 → False) ∧ p1) ∧ (p4 ∧ (((False → p2) → p2) ∨ (p2 → (p4 ∧ p1))))) ∧ True) → p3)) ∨ p3) := by
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
  cases h9
  case inl h10 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h11 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h12 := h6 h11
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h14 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h15 := h6 h14
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301845379669746107231382806637 : (False ∨ ((p5 ∨ p4) ∨ (p3 ∨ ((True ∨ p4) ∧ ((False ∨ (p5 ∨ ((False ∧ True) → (p1 ∨ ((p2 ∧ (p1 ∨ p2)) → p2))))) ∧ (False → p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66655731580311845406748355070 : ((True → ((p3 ∨ (((p4 → (p5 ∧ False)) ∨ p2) ∧ p4)) ∧ ((((p5 ∧ p1) ∨ ((((p3 ∨ p5) → p5) ∨ p2) → p4)) ∧ p2) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315860449532189020182619368596 : (p3 ∨ ((p3 → p4) → ((p2 → ((p5 ∨ ((True ∧ True) ∨ p2)) → False)) → (((p4 → p3) ∨ ((((p3 ∧ p2) → p4) ∧ True) → True)) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156965898441690467470434638955 : (((((False ∧ (p3 → (True ∨ (p1 ∧ p4)))) → (p4 → False)) ∧ ((p4 ∨ p5) ∧ (p3 ∨ p4))) ∨ False) ∨ ((p5 → True) ∧ (p2 ∨ (True ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_808213236163948169067220876469 : (((p4 → (p4 ∧ ((((p3 → ((p2 ∨ (p5 → (True → (p5 ∨ True)))) ∨ p2)) ∨ (((p3 ∧ (p2 → p2)) → False) ∧ p5)) → p2) ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253906703185996001602860723542 : ((p1 ∧ p4) → (((((p3 ∨ ((p2 → p1) → p5)) ∨ p2) → (p5 → p5)) → ((p3 ∨ (((p2 ∧ p4) ∨ (p5 ∨ p1)) ∨ True)) ∧ True)) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
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
theorem thm_5_vars_755421739092041548227159494511 : (((p1 ∧ ((((False → p1) ∨ (((True ∧ True) → p3) ∨ True)) → ((p3 → ((True ∧ p4) → ((p1 ∧ (True ∧ p1)) ∨ p5))) ∧ p5)) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165459114351504779051466275089 : ((((p3 → (p1 ∨ p5)) ∧ (((True ∧ p2) ∧ p1) ∨ False)) ∧ (p5 → ((p5 → p2) ∧ p2))) ∨ (False ∨ ((p3 ∧ False) → (p2 → (p3 → p5))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118336908625743388260173173418 : ((p2 ∨ ((((p2 → False) ∧ (((p4 ∧ False) ∨ p5) ∧ (p5 → ((p4 ∧ (True ∨ p5)) ∧ ((p5 ∧ p4) → p3))))) ∨ p4) ∨ True)) ∨ (p3 → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60210103960590056865817182209 : (((True → False) → ((((p3 ∨ ((((False ∧ True) ∨ p3) ∧ p4) ∧ p5)) ∨ (((p1 → p3) → p2) ∧ (p5 ∨ (True ∧ p5)))) ∧ p5) ∧ True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350396479814778030818492933537 : (p4 → (((p1 → (((((True ∧ p1) ∧ (((False → (p1 ∨ p4)) → (((p4 ∨ p5) ∨ p1) → p3)) → p4)) ∧ p4) ∧ p3) ∧ p2)) ∧ p1) → p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624938734878383429718205245114 : ((((p5 ∨ ((p3 → p2) → ((((((True ∧ (p2 ∨ (False ∧ ((p2 ∨ (False ∨ p3)) → True)))) ∨ True) ∧ p3) → True) ∧ p1) ∨ p4))) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_1468013450100363452706114596 : ((((p3 → ((((((p3 → ((p4 ∧ p2) ∧ p5)) ∧ p1) → p5) ∧ False) ∨ p4) ∧ ((p4 → p5) ∨ p5))) ∨ p3) ∨ True) ∨ (p3 ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698144710466873061018419274811 : ((((((((((False → True) ∧ True) → p5) → p2) ∨ p1) ∨ p4) → p3) ∨ ((((p4 ∧ p3) ∨ (((p3 ∨ p5) ∨ False) → p4)) ∧ p3) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40352760674453002802328051726 : (((((((p2 ∨ False) → (False ∧ ((False → p5) ∨ (((p5 ∧ (((p3 ∧ True) ∨ p5) ∧ p2)) → False) ∨ p5)))) ∨ p2) → p2) ∨ True) ∨ p4) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65366190336962926647693550072 : ((p3 ∨ (((((p3 ∨ p4) ∧ p5) ∧ ((p4 → p1) ∧ (p4 → p3))) ∨ p3) → (p1 ∨ (p5 ∧ ((True ∨ (p5 ∧ (False → p5))) → p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337959940343647895303967081225 : (p1 → ((p4 ∧ ((False ∧ p5) ∨ (False ∨ (False ∧ ((p1 → True) ∨ p5))))) ∨ (p1 ∨ (((((p1 ∧ (p4 ∧ False)) ∨ True) → p2) → p1) ∧ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257792347972005199664608355109 : ((p3 ∨ p5) → ((((p1 ∨ (p5 ∧ (((False → p2) ∨ p5) ∧ p3))) ∧ (p3 → (p2 → (p5 ∧ (p1 → (p4 ∧ p5)))))) ∨ (False → True)) ∨ p1)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780957647280289537834782365800 : (((p2 ∨ (((True ∨ p2) ∧ p2) → (((((False → p5) ∨ p5) ∨ (((p4 → False) ∧ (p5 ∧ p3)) → p3)) → p4) ∨ (p3 → (p2 ∨ p4))))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157329728989134786288188423079 : (((False ∨ (((p2 → p2) ∨ (p1 → ((((p3 ∨ p1) ∧ False) → True) ∨ (p1 → p3)))) ∧ p1)) → p2) ∨ ((p2 ∨ ((p5 ∨ True) ∨ p2)) ∨ p3)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669289246519717891686242489768 : (((((p5 → (False ∧ (p2 ∨ (p4 ∧ ((p5 ∧ p1) → ((((True → (p3 → p4)) → p5) → True) ∧ False)))))) → p1) ∨ (p2 ∨ (p3 → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49040706751504144435721608964 : ((((p2 ∨ (True → ((p4 ∨ (False ∨ ((False ∨ False) → ((p4 ∧ (p5 ∨ p3)) ∨ True)))) ∧ (p5 ∨ False)))) → p4) ∨ ((True ∨ p2) ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156916711573716213598609578602 : (((((p2 → (p5 → ((p4 ∨ p3) ∧ p5))) → ((p4 ∧ p5) → ((p3 ∨ False) → False))) → p4) ∨ True) ∨ (p4 → (False ∧ (p1 → (p2 ∨ True))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134688904212028842525789054160 : (((((p5 ∨ ((p5 ∨ p3) → p1)) ∧ p2) → ((p4 ∨ p3) → (p3 ∨ (p5 ∨ (((p2 ∧ False) ∧ p1) → p1))))) → False) ∨ ((False → p2) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699664847582365813583580477423 : (((((False ∧ (False → ((p3 → p2) ∧ ((p5 ∧ p3) → p5)))) → p3) → ((p2 ∨ ((True ∧ p2) ∧ ((p2 ∧ True) ∨ (p3 ∧ p3)))) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348259278432805526321168561606 : (p3 → (True ∧ (((p5 ∨ ((p1 ∨ ((True ∨ ((False → (p1 ∧ False)) ∨ (p5 → p1))) ∨ p1)) → p3)) → False) ∨ (((False ∨ p3) → False) → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40140178101850704942236164377 : ((((((((((((p4 → False) → p4) ∨ p2) ∨ p5) ∧ False) ∨ p1) → False) → (True → False)) → (False ∨ (p4 ∧ (p1 ∧ p3)))) ∧ p3) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190119840502646946831127919151 : ((((p2 ∧ (False ∨ True)) ∨ (True → (False ∧ p5))) ∧ p5) ∨ ((False ∨ True) → ((((False ∨ p4) ∨ ((p4 ∨ p2) → True)) → False) → (p3 ∧ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : ((False ∨ p4) ∨ ((p4 ∨ p2) → True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h5
    -- False on the left can always be used.
    apply False.elim h7
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h10 : ((False ∨ p4) ∨ ((p4 ∨ p2) → True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h12 := h2 h10
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44674943727590221835233612119 : ((((((p1 ∨ p4) ∨ p1) ∧ (p5 ∧ p2)) → ((p3 ∧ ((True ∨ p3) ∧ (True → (((False ∧ p2) ∧ p4) ∧ p2)))) → (p2 ∨ p3))) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113495752591857144399763433528 : (((((True ∧ (p2 ∨ ((False ∨ ((((p4 ∧ False) → p5) → p2) ∧ p3)) → p5))) → p5) ∨ (p1 → (True → p1))) ∨ (False → True)) ∨ (p1 ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_806451907573043242161385651119 : (((p4 → ((((p1 → (((True ∨ False) → (p4 ∧ (p5 ∧ p2))) ∨ p3)) ∧ (((p4 → (p3 ∧ (p2 ∧ p5))) → p2) ∧ p5)) ∨ False) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683720676131976325139897869584 : (((((p1 → (False ∧ ((p3 → ((((p5 ∧ True) ∨ p4) → p5) ∨ (p4 ∧ p5))) ∨ p2))) ∧ p3) ∨ ((p1 → (False → (False ∨ True))) ∧ True)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204430574725779640380286647154 : (((((p4 ∧ p3) ∧ p4) ∧ p4) ∨ p3) ∨ (p5 ∨ (False → ((((p2 ∧ p4) → p5) ∧ (((p1 ∨ ((p4 ∧ p4) ∧ p5)) ∨ p3) ∧ p5)) ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251144405587150708973303695306 : ((p2 → False) ∨ ((False ∨ True) ∧ ((((p4 ∨ p5) ∧ ((True ∧ (p5 → p5)) → p1)) ∨ p2) → (False ∨ (p4 ∨ (False → (p1 → (True → False)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- Implications on the right can always be decomposed.
      intro h9
      -- False on the left can always be used.
      apply False.elim h7
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- Implications on the right can always be decomposed.
    intro h12
    -- Implications on the right can always be decomposed.
    intro h13
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_90052724142177638808395602744 : ((((p5 → p5) ∨ p3) → ((((p4 → ((p5 ∨ True) ∧ ((p2 ∨ (p4 ∧ p1)) ∨ (p5 → p3)))) ∨ p3) ∨ (False ∨ p4)) ∧ (p3 ∧ p3))) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p5 → p5) ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_799998158939018546307059781424 : (((p2 → ((((((True ∨ p3) → (True → (((p4 → p3) ∨ True) ∨ ((p1 ∧ p4) ∧ p1)))) ∨ p3) → (p1 ∨ p4)) ∨ (p2 ∨ p2)) ∧ p2)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337529930940668440263679775628 : (p1 → ((((p4 ∧ (p5 ∨ ((p1 ∨ (p4 ∧ ((False ∨ True) ∨ (p5 ∨ False)))) ∧ p2))) ∨ False) ∨ (False ∨ p1)) ∨ (((True → p5) ∧ False) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135629590211580334942401590494 : ((((((True → ((((p5 ∨ p5) ∨ p1) → p2) → p2)) ∨ (p1 → p1)) ∨ p1) ∨ p4) → (p3 ∧ ((False ∨ p1) ∨ p2))) ∨ (True ∨ (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184455896903022124752213020660 : (((p4 ∨ ((p2 → True) → ((False ∨ True) → p2))) ∧ (p5 → False)) ∨ (((False → p5) → True) → (((((p3 ∧ True) ∧ p4) → True) ∧ p4) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148193378095135201428386072660 : ((((p2 ∧ (p4 → True)) ∧ (p2 ∧ ((((p2 ∨ p5) → False) ∨ (p1 → True)) → p2))) ∧ ((True ∧ p4) ∧ False)) ∨ (((p2 → p2) ∨ p1) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229040301433471077659879913683 : ((p5 ∨ (p1 ∨ p4)) ∨ (((((p3 ∨ p5) → (p5 → (True ∨ p3))) ∨ p2) → (((p5 → p2) → p3) → (True ∧ (False ∨ (p2 → p3))))) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : (p5 → p2) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h5
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h10 : (p5 → p2) := by
      -- Implications on the right can always be decomposed.
      intro h11
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h12 := h2 h10
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_715693456312778860268396955827 : ((((((p4 ∧ True) ∧ True) ∨ p1) ∧ ((True ∧ ((p5 ∨ True) → True)) ∧ ((False ∨ (False ∨ True)) → (p2 ∨ (p4 ∧ (p5 ∨ (p3 ∧ p5))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357467212861282772773749765697 : (p5 → ((p3 → p3) → ((True → p1) → (((p2 ∧ (p5 ∨ (True ∨ p2))) ∨ (False ∧ (False → (p4 ∧ p4)))) → ((False → (p4 → p5)) → p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
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
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h17 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h18 := h3 h17
        -- One of the premise coincides with the conclusion.
        exact h18
  case inr h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h19.left
    let h21 := h19.right
    -- False on the left can always be used.
    apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613645364756646431929578088503 : (((((((p3 → (((p4 ∨ p5) → p2) ∨ ((p5 ∨ (False ∧ p2)) ∧ p4))) → p2) → (p2 ∧ (p1 ∨ False))) ∧ (p5 → (p5 ∧ p3))) ∨ True) ∨ p3) ∧ True) := by
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



