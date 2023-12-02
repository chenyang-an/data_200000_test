variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116976526079701218524603865436 : (((p4 ∧ p5) → (((p3 → True) → ((p1 → (False ∧ (p3 ∨ ((p3 ∧ ((p5 ∧ p5) ∧ (p3 ∧ p5))) ∨ True)))) ∧ p4)) ∧ False)) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_76596579608054268158564363138 : (((((p2 ∨ (False ∧ (False → p2))) → (((False ∨ p5) ∨ (p1 ∧ p5)) → ((p4 ∧ p3) ∨ True))) ∨ ((p5 ∧ (p2 ∨ p1)) ∧ p3)) → p5) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p2 ∨ (False ∧ (False → p2))) → (((False ∨ p5) ∨ (p1 ∧ p5)) → ((p4 ∧ p3) ∨ True))) ∨ ((p5 ∧ (p2 ∨ p1)) ∧ p3)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
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
        cases h3
        case inl h8 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h9 =>
          -- Conjunctions on the left can always be decomposed.
          let h10 := h9.left
          let h11 := h9.right
          -- False on the left can always be used.
          apply False.elim h10
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h16.left
        let h18 := h16.right
        -- False on the left can always be used.
        apply False.elim h17
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h19 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316571997045371115507690754383 : (p3 ∨ (p3 ∨ ((False ∧ (p2 → ((((p3 ∨ False) ∧ p1) → p4) → True))) ∨ (p5 ∨ ((((p5 ∧ p3) → p2) ∨ p5) ∨ ((p3 ∨ p2) ∨ True)))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_637617813532195276774547443974 : (((((p3 ∧ ((p4 → ((p4 → p5) ∨ p5)) → (p5 ∨ p4))) ∨ ((p3 ∧ (False ∨ (((False ∨ (p5 ∨ p4)) → p3) ∨ p5))) ∧ p1)) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60468167532008909257485372506 : (((p5 → p3) → (p5 ∨ ((p4 ∧ ((p4 ∧ (((False ∧ p1) ∧ False) → ((p2 ∨ p3) ∨ (False ∧ p5)))) ∧ (p4 ∧ False))) ∨ (False → False)))) ∨ p5) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186315080304017606487500114307 : ((((p1 ∧ (p5 → (p3 ∨ (True ∧ p2)))) ∨ (True → p1)) → p2) → ((((((p5 ∧ p3) ∧ p3) ∨ p4) ∧ p4) ∧ (False → p2)) ∨ (True → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247285058134127194194284269948 : ((False ∨ False) ∨ ((((((p3 ∨ (((p2 ∧ p3) ∨ p5) ∧ p4)) → (p2 → (p5 ∧ p1))) → p5) ∧ (p3 ∧ ((True ∨ p4) ∨ False))) ∨ True) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_625164659678490439427997884492 : ((((True → (((p4 ∧ (p4 → (p4 ∧ p2))) ∧ False) ∧ (p4 → ((p2 ∧ True) ∧ ((p3 ∨ p3) ∧ ((p2 ∨ (p5 ∨ p1)) ∨ True)))))) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_225525361219931931853207890414 : (((True → True) ∧ p3) ∨ ((((p2 → False) ∧ (p5 → p3)) ∧ (p2 ∨ p3)) → ((p1 ∧ p3) ∨ (p2 → (p4 → (((p2 ∧ p4) ∨ p3) → p1)))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h6 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h7 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h8 := h4 h7
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- Implications on the right can always be decomposed.
    intro h12
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h16 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h10
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h17 := h4 h16
      -- False on the left can always be used.
      apply False.elim h17
    case inr h18 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h19 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h10
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h20 := h4 h19
      -- False on the left can always be used.
      apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48861071127682315523989315215 : (((p4 ∨ ((((True → (((((p3 → p4) ∨ p5) ∧ (p2 → p3)) ∧ (p1 ∨ p4)) ∧ p3)) → p1) ∨ p5) → p3)) ∧ (p4 → (False → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232397771322118737324814245472 : (((p5 → p3) → p4) → (True ∧ (((((p4 ∨ (p5 → p3)) ∨ (p4 → (p5 → (p4 → (True ∨ p5))))) → p1) → (p4 ∨ p4)) ∨ (p1 → p1)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42238300086744691402524586269 : (((False ∧ ((p1 → False) → (p3 ∧ (p2 → (((p2 → p3) → p4) ∨ (False ∧ ((p3 ∨ ((False → p2) ∨ (p1 ∨ p2))) ∧ p4))))))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134318750761968798245462385177 : (((p1 ∧ (((p1 → (p3 ∧ (((p4 ∧ (True ∨ (p4 → (p5 ∨ p3)))) ∧ (p2 ∨ True)) ∨ p5))) → p2) → p1)) ∨ True) ∨ (p5 ∨ (p2 → p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164497746365827470476956846827 : (((((p3 → (False ∧ p1)) ∧ (p5 ∨ ((p4 → p3) → ((p1 ∧ False) ∨ p1)))) → p4) ∧ p3) ∨ (p4 ∨ (((p1 ∨ p1) ∨ (True ∨ p3)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165535663632269281577056497325 : ((((((p2 ∧ p2) ∨ (True ∧ p4)) ∧ p1) ∧ p4) ∧ ((p5 ∨ ((p5 ∨ p5) ∨ p1)) ∧ p1)) ∨ ((True ∧ ((False ∧ p1) ∧ p2)) → (p2 → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45443867498860019750690309817 : (((True ∨ ((p3 ∨ ((p3 → p5) → (False → p4))) ∨ ((False ∧ False) → ((False ∧ (p2 ∨ (False ∧ p4))) → ((p3 ∧ p3) ∨ p1))))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233278122150449647309871936026 : ((True ∨ (True ∨ p1)) → ((True → (p3 ∧ p3)) → ((((p4 ∧ ((((False ∨ p5) ∨ (True → p2)) → True) ∧ p4)) ∧ p4) ∨ p4) ∨ (True ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116638645564046355874396488024 : (((p2 → False) ∧ (((((p3 → (p5 ∨ p3)) ∨ True) ∧ p3) ∨ ((False ∧ p3) ∧ p4)) → ((p4 → (p1 ∨ p5)) ∧ (p3 ∨ True)))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345534965699783669009590974469 : (p3 → ((((p5 ∨ p2) ∧ ((True ∨ False) → (False ∨ False))) ∧ (((p1 ∧ p3) ∧ (p5 ∧ (((p2 ∧ p1) ∧ p2) ∧ True))) → (p3 ∧ False))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166421280858342476601525921988 : ((p1 ∨ ((p2 ∨ (((True → p5) → (p5 ∧ p2)) → True)) → (False ∧ (True → (p3 ∧ p2))))) ∨ (p1 ∨ ((True ∨ p1) ∧ ((False ∨ False) → p5)))) := by
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
theorem thm_5_vars_299449451049091873060526183076 : (False ∨ ((p2 ∨ (p5 ∨ (p4 ∧ (p5 → (((p4 → ((p2 ∨ (True ∨ (True ∧ False))) → (p5 ∨ p4))) → (False ∨ False)) → (False ∨ True)))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_266042022747108635564769485710 : (True ∧ (p1 → (False ∨ (p4 ∨ (((p2 ∧ ((p2 ∨ (p2 → p4)) ∨ True)) → ((True → p2) → ((((p3 ∨ p1) ∧ p2) ∨ p5) ∨ p2))) ∨ p1))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252630042220324347635005402712 : ((p5 → p4) ∨ (((p4 ∨ (((False → ((((p3 ∨ False) ∧ (True ∧ p2)) ∧ (p1 ∨ False)) ∧ p1)) ∨ (p2 → False)) → (p2 → True))) → p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_7705950883243450506239007801 : (((((p3 ∧ (((False ∨ p2) → (((p3 ∧ p5) → ((p5 ∧ False) ∨ ((False → (p1 ∨ p3)) ∨ p5))) → p3)) ∨ p2)) ∨ False) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678654195373883461320963314240 : (((((True ∧ False) ∨ ((p2 → p4) → (((p4 ∧ p1) ∧ ((((p5 ∧ p1) ∨ p1) ∨ True) ∨ p1)) → False))) ∨ ((p2 ∨ True) ∨ (p2 → False))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_322281033357995677133657904576 : (p5 ∨ ((((((False ∨ True) ∧ p3) → ((False ∨ ((False ∨ ((True ∨ p1) → p2)) ∧ (((p1 ∧ False) ∨ False) → False))) ∧ p3)) ∨ False) → p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325856038762404890660776914695 : (p5 ∨ (p4 ∨ (((p1 ∨ (p5 ∨ ((True ∧ True) ∧ ((True → (p4 ∨ p5)) ∨ p2)))) ∨ (p1 → ((True ∨ ((p4 ∧ p5) ∨ p2)) ∧ p4))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49330204193254105739252312147 : (((p5 ∨ ((((p4 ∧ ((p3 ∨ p4) ∨ (((False → p1) ∨ p2) ∧ True))) → ((p4 → p2) ∨ p3)) ∨ p5) → p5)) ∨ ((p4 → p4) ∨ p2)) ∨ False) := by
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
theorem thm_5_vars_59534761835780292626609180479 : (((p2 → p5) ∨ (p5 ∨ (p2 ∧ (((((True ∧ ((p3 ∧ p4) ∨ p1)) → True) ∧ ((p1 ∨ p2) ∧ ((p4 → p4) ∧ True))) → p3) ∧ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729476992921709613944189469251 : (((((False ∨ False) ∨ p4) → ((False ∧ p1) ∨ (((p2 ∧ (True ∨ ((p2 ∨ (p4 ∧ p4)) ∧ ((True ∧ p3) ∧ p3)))) → (p5 → False)) ∨ True))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- False on the left can always be used.
      apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_33450592114145635126537887124 : ((p4 ∨ ((p3 ∨ (p5 ∨ (((True ∨ p1) → p3) → p1))) → ((p2 ∨ p4) → (p1 ∨ (p2 ∨ (p4 ∨ (True ∨ (p3 ∨ (p1 → p4))))))))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h3
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208859216364568882882200679838 : ((p4 ∧ ((p1 ∨ (p5 → p3)) ∨ p1)) → (((p4 ∨ p1) ∨ p2) → (((((p5 ∨ p4) → p1) ∨ False) ∧ ((p1 → True) ∨ False)) → (p4 ∧ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h2
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Conjunctions on the left can always be decomposed.
          let h10 := h1.left
          let h11 := h1.right
          -- Disjunctions on the left can always be decomposed.
          cases h11
          case inl h12 =>
            -- Disjunctions on the left can always be decomposed.
            cases h12
            case inl h13 =>
              -- One of the premise coincides with the conclusion.
              exact h10
            case inr h14 =>
              -- One of the premise coincides with the conclusion.
              exact h10
          case inr h15 =>
            -- One of the premise coincides with the conclusion.
            exact h10
        case inr h16 =>
          -- Conjunctions on the left can always be decomposed.
          let h17 := h1.left
          let h18 := h1.right
          -- Disjunctions on the left can always be decomposed.
          cases h18
          case inl h19 =>
            -- Disjunctions on the left can always be decomposed.
            cases h19
            case inl h20 =>
              -- One of the premise coincides with the conclusion.
              exact h17
            case inr h21 =>
              -- One of the premise coincides with the conclusion.
              exact h17
          case inr h22 =>
            -- One of the premise coincides with the conclusion.
            exact h17
      case inr h23 =>
        -- Conjunctions on the left can always be decomposed.
        let h24 := h1.left
        let h25 := h1.right
        -- Disjunctions on the left can always be decomposed.
        cases h25
        case inl h26 =>
          -- Disjunctions on the left can always be decomposed.
          cases h26
          case inl h27 =>
            -- One of the premise coincides with the conclusion.
            exact h24
          case inr h28 =>
            -- One of the premise coincides with the conclusion.
            exact h24
        case inr h29 =>
          -- One of the premise coincides with the conclusion.
          exact h24
    case inr h30 =>
      -- False on the left can always be used.
      apply False.elim h30
  case inr h31 =>
    -- False on the left can always be used.
    apply False.elim h31
  -- Conjunctions on the left can always be decomposed.
  let h32 := h3.left
  let h33 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h32
  case inl h34 =>
    -- Disjunctions on the left can always be decomposed.
    cases h33
    case inl h35 =>
      -- Disjunctions on the left can always be decomposed.
      cases h2
      case inl h36 =>
        -- Disjunctions on the left can always be decomposed.
        cases h36
        case inl h37 =>
          -- Conjunctions on the left can always be decomposed.
          let h38 := h1.left
          let h39 := h1.right
          -- Disjunctions on the left can always be decomposed.
          cases h39
          case inl h40 =>
            -- Disjunctions on the left can always be decomposed.
            cases h40
            case inl h41 =>
              -- One of the premise coincides with the conclusion.
              exact h41
            case inr h42 =>
              -- We want to use the implication h34 based on <expert-advice>. So we show its premise.
              have h43 : (p5 ∨ p4) := by
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- One of the premise coincides with the conclusion.
                exact h38
              -- We have shown the premise of h34, we can now drive its conclusion.
              let h44 := h34 h43
              -- One of the premise coincides with the conclusion.
              exact h44
          case inr h45 =>
            -- One of the premise coincides with the conclusion.
            exact h45
        case inr h46 =>
          -- Conjunctions on the left can always be decomposed.
          let h47 := h1.left
          let h48 := h1.right
          -- Disjunctions on the left can always be decomposed.
          cases h48
          case inl h49 =>
            -- Disjunctions on the left can always be decomposed.
            cases h49
            case inl h50 =>
              -- One of the premise coincides with the conclusion.
              exact h50
            case inr h51 =>
              -- One of the premise coincides with the conclusion.
              exact h46
          case inr h52 =>
            -- One of the premise coincides with the conclusion.
            exact h52
      case inr h53 =>
        -- Conjunctions on the left can always be decomposed.
        let h54 := h1.left
        let h55 := h1.right
        -- Disjunctions on the left can always be decomposed.
        cases h55
        case inl h56 =>
          -- Disjunctions on the left can always be decomposed.
          cases h56
          case inl h57 =>
            -- One of the premise coincides with the conclusion.
            exact h57
          case inr h58 =>
            -- We want to use the implication h34 based on <expert-advice>. So we show its premise.
            have h59 : (p5 ∨ p4) := by
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h54
            -- We have shown the premise of h34, we can now drive its conclusion.
            let h60 := h34 h59
            -- One of the premise coincides with the conclusion.
            exact h60
        case inr h61 =>
          -- One of the premise coincides with the conclusion.
          exact h61
    case inr h62 =>
      -- False on the left can always be used.
      apply False.elim h62
  case inr h63 =>
    -- False on the left can always be used.
    apply False.elim h63



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301769512562848632637274354075 : (False ∨ ((True ∧ p1) ∨ ((((((p5 → p2) ∧ p3) ∧ p1) → (p3 → p4)) → (False ∧ ((p4 ∧ p4) ∧ p5))) → ((p4 ∨ (p4 ∧ p4)) → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h4 : ((((p5 → p2) ∧ p3) ∧ p1) → (p3 → p4)) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the left can always be decomposed.
      let h7 := h5.left
      let h8 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h7.left
      let h10 := h7.right
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h11 := h1 h4
    -- We need to get the left conjuct of h11 based on <expert-advice>.
    let h12 := h11.left
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h16 : ((((p5 → p2) ∧ p3) ∧ p1) → (p3 → p4)) := by
      -- Implications on the right can always be decomposed.
      intro h17
      -- Implications on the right can always be decomposed.
      intro h18
      -- Conjunctions on the left can always be decomposed.
      let h19 := h17.left
      let h20 := h17.right
      -- Conjunctions on the left can always be decomposed.
      let h21 := h19.left
      let h22 := h19.right
      -- One of the premise coincides with the conclusion.
      exact h15
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h23 := h1 h16
    -- We need to get the left conjuct of h23 based on <expert-advice>.
    let h24 := h23.left
    -- False on the left can always be used.
    apply False.elim h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61409144584673686082058841960 : ((p1 ∧ (((((p4 ∧ (p3 → False)) → ((p2 → ((p3 ∨ (False → ((True → True) ∧ True))) → True)) ∨ (p5 → p4))) ∧ p2) ∧ True) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116441674641021138421719970599 : (((p3 → (p5 ∨ p4)) → ((False ∧ (p5 ∧ p2)) ∧ (((False → ((p2 → True) ∧ ((p3 ∧ True) → (True → p4)))) ∧ p3) → p5))) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256276745417258679173037708005 : ((False ∨ p1) → ((p4 ∧ (((True ∨ p4) → (p3 ∨ ((((((True → (p4 ∧ p5)) ∧ p5) → p4) ∧ p5) → (p3 ∨ p5)) ∧ p2))) ∨ p5)) ∨ p1)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177792262394344709039952171234 : (((False ∨ ((p5 ∨ p4) ∨ (p1 ∨ (((True ∨ p4) ∨ p3) ∨ p5)))) ∧ False) ∨ ((p5 ∨ (((False ∨ (p5 ∧ False)) ∨ p1) ∨ True)) ∨ (p4 ∨ p1))) := by
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
theorem thm_5_vars_43973357242891423969714523172 : ((((p1 → ((((((True ∨ (p3 ∧ True)) → p3) ∧ (p2 ∨ (p2 ∨ p4))) ∨ (p2 → (p2 → p2))) → p5) → p1)) ∨ (p1 ∨ p5)) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_651215193213779087154335246368 : (((((False → ((True ∨ False) ∧ p4)) → ((p3 → (p5 ∧ (((p1 ∧ True) → (p5 ∧ p2)) → ((p5 ∨ False) ∨ False)))) ∨ p2)) ∧ (p1 → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_767987856229252226647989173838 : (((p5 ∧ ((p1 → ((p2 ∧ (p3 ∨ ((p3 ∧ ((p3 → (p4 → p2)) ∧ True)) ∧ p5))) ∨ (((p4 ∨ False) ∧ (p3 → True)) ∨ p4))) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258800773800087700420084479123 : ((True → False) → (True ∧ ((p1 ∧ ((((p5 ∧ ((True ∨ False) ∨ p1)) ∧ p2) ∧ p3) → (p4 ∨ (False ∧ (p4 ∨ p3))))) ∨ ((True ∧ p4) → True)))) := by
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
theorem thm_5_vars_299155473813647506257996985243 : (False ∨ (((p4 ∨ ((p1 → False) ∨ (((((p5 → p5) ∨ ((False ∨ p2) ∧ p2)) ∧ False) ∨ p3) ∨ ((p3 → p4) → (p3 ∨ p3))))) ∨ True) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164813006936829286599160271598 : ((((False → p1) ∧ (p4 ∧ ((((True → (p3 ∧ False)) → (p1 ∧ False)) → p4) ∧ True))) ∨ p5) ∨ (False ∨ (p3 → (((p5 → p3) ∨ p1) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117079007349154426304857485217 : (((False → False) → (((p4 → p5) ∧ (((((False ∨ p3) ∨ (False ∨ p5)) → ((True → p2) ∧ False)) → (False ∧ True)) ∨ p2)) ∨ False)) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248620757953667843200463627838 : ((p3 ∨ p1) ∨ (((False ∧ ((False ∨ True) ∨ (False → ((p3 → p3) ∧ ((p2 → (p5 ∧ (p1 → (p5 → True)))) ∧ (False → False)))))) ∧ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171496629561375657916147438030 : (((p4 → ((((((p2 ∨ p5) ∧ p4) ∨ (False → p4)) → p5) ∧ p4) ∨ p4)) ∧ p3) ∨ (p2 → ((((False → p2) ∨ (p5 ∨ p4)) ∨ p5) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305616400364188060881188413525 : (p1 ∨ ((((p1 ∧ (False → (p3 ∧ (True ∧ p3)))) → False) → (p2 ∧ p2)) → (((False ∧ (((p5 ∧ True) ∧ (p4 ∧ p3)) → p2)) ∨ True) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137625308381640584215229213656 : ((False ∨ ((((((p2 ∨ ((p2 ∧ p3) ∧ p1)) ∨ p2) ∧ p2) ∧ False) → (p4 ∧ (True ∧ (True ∧ (False ∨ p3))))) → p1)) ∨ ((p4 ∨ True) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_642581247227057231673846108577 : ((((p1 ∧ (((p5 → (False ∨ (p5 ∨ p3))) ∨ (p5 → ((((p3 ∧ True) ∧ (False ∧ (p2 ∨ True))) ∧ (p5 ∧ False)) ∧ False))) ∨ p2)) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204348825630644917507550771437 : (((False ∨ ((p2 ∧ p1) ∨ p1)) ∧ True) ∨ (False ∨ ((p5 → (((p2 → False) ∧ p4) → ((p5 → False) ∨ (p2 → (p4 → (p2 → True)))))) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_33895087434309419128138936678 : ((p5 ∨ ((p3 ∨ (p5 ∧ (p5 ∧ p3))) ∨ ((((p2 ∧ p5) ∧ (p3 ∨ ((p4 ∧ True) ∧ p3))) ∧ True) → (p5 ∧ (p5 ∧ (p5 ∨ p4)))))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h8 =>
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- One of the premise coincides with the conclusion.
    exact h7
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h14 := h1.left
  let h15 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h16 := h14.left
  let h17 := h14.right
  -- Conjunctions on the left can always be decomposed.
  let h18 := h16.left
  let h19 := h16.right
  -- Disjunctions on the left can always be decomposed.
  cases h17
  case inl h20 =>
    -- One of the premise coincides with the conclusion.
    exact h19
  case inr h21 =>
    -- Conjunctions on the left can always be decomposed.
    let h22 := h21.left
    let h23 := h21.right
    -- Conjunctions on the left can always be decomposed.
    let h24 := h22.left
    let h25 := h22.right
    -- One of the premise coincides with the conclusion.
    exact h19
  -- Conjunctions on the left can always be decomposed.
  let h26 := h1.left
  let h27 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h28 := h26.left
  let h29 := h26.right
  -- Conjunctions on the left can always be decomposed.
  let h30 := h28.left
  let h31 := h28.right
  -- Disjunctions on the left can always be decomposed.
  cases h29
  case inl h32 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h31
  case inr h33 =>
    -- Conjunctions on the left can always be decomposed.
    let h34 := h33.left
    let h35 := h33.right
    -- Conjunctions on the left can always be decomposed.
    let h36 := h34.left
    let h37 := h34.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h31
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208461555839053458886809269496 : (((p2 → p1) ∨ (p5 ∨ (p2 ∧ p4))) → ((p4 → (p5 ∧ (((True ∧ p5) ∨ True) ∨ ((p4 ∨ False) ∧ ((p3 → p2) ∨ p4))))) ∨ (p5 → True))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233530961910903509510666537767 : ((p1 ∨ (p2 ∨ p1)) → ((p3 → ((((p5 → (p4 → False)) → ((p2 ∨ p1) ∧ True)) ∧ (p4 ∨ True)) → (p1 ∧ p4))) ∨ ((p2 ∨ p4) → True))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352741662472659738958194347287 : (p4 → ((True ∧ p2) → (((p1 ∨ (((p5 → ((p1 → ((p4 ∧ (p5 ∨ p4)) ∧ p4)) → p4)) → (p1 → (p4 → False))) ∨ p4)) ∨ p1) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140737177207988100122694716692 : ((((((((p1 ∧ p3) → p3) ∧ True) ∨ False) ∨ ((False ∨ p2) ∧ p1)) → p4) → (p4 → ((False ∨ (p4 ∨ True)) → p1))) → ((p5 → False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264389269818537557632439559221 : (True ∧ (((p1 ∧ (p3 → False)) → p2) ∨ (p4 ∨ ((p4 → (True ∨ (False ∨ (False → p4)))) → ((((p5 → (p4 ∨ p3)) ∨ p3) ∨ True) ∨ p1))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52858115161558208010311427828 : (((True ∧ ((p1 ∨ (p4 ∧ True)) ∨ ((p5 ∨ (p5 → p5)) ∧ (False → p5)))) → (((p5 ∨ ((p5 ∨ p3) → (p2 → p2))) → p3) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_950322306310579733998736511284 : (((((p3 → False) → p3) ∧ ((True ∧ ((((p4 ∨ True) ∨ p2) → (((True → (False ∧ p4)) → False) ∧ False)) ∨ False)) ∧ ((p3 ∨ True) ∨ p1))) → p5) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h11 : ((p4 ∨ True) ∨ p2) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h12 := h8 h11
        -- We need to get the right conjuct of h12 based on <expert-advice>.
        let h13 := h12.right
        -- False on the left can always be used.
        apply False.elim h13
      case inr h14 =>
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h15 : ((p4 ∨ True) ∨ p2) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h16 := h8 h15
        -- We need to get the right conjuct of h16 based on <expert-advice>.
        let h17 := h16.right
        -- False on the left can always be used.
        apply False.elim h17
    case inr h18 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h19 : ((p4 ∨ True) ∨ p2) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h20 := h8 h19
      -- We need to get the right conjuct of h20 based on <expert-advice>.
      let h21 := h20.right
      -- False on the left can always be used.
      apply False.elim h21
  case inr h22 =>
    -- False on the left can always be used.
    apply False.elim h22
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135494628102885048522084537543 : (((True ∧ (p4 ∨ (((p3 ∨ (((p4 → True) ∨ True) → (p1 ∧ False))) ∨ (True ∨ p1)) ∨ p4))) → (p3 ∨ (True → p1))) ∨ ((False ∧ p3) → p5)) := by
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
theorem thm_5_vars_234022772181867937620991460415 : ((p5 ∨ (p5 ∨ p4)) → ((p1 → (False ∧ False)) ∨ (p3 → (((((((p2 ∨ (p3 → True)) ∧ (False → p2)) ∧ p1) → p1) ∧ p2) → p3) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
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
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h9
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- One of the premise coincides with the conclusion.
      exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219273704621037833837000386709 : ((p1 ∨ (True → (True → False))) → ((p1 ∧ False) ∨ ((p4 → (p2 ∨ (((False → p1) → (((p4 → p4) ∧ p5) → (p2 ∧ p3))) ∨ p4))) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h8 := h6 h7
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610338902402886785887097422461 : ((((((((p5 ∨ ((((True → (p2 ∨ (p3 → (p3 ∧ (p1 ∨ True))))) ∧ p1) → p2) ∨ p1)) → (p4 → p5)) ∧ True) → p2) → False) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49089518882911089847315882353 : ((((p2 ∧ ((p1 ∨ (p3 ∨ (p1 ∧ p4))) ∨ (p3 ∨ (p4 ∧ (p2 ∧ (p3 → p1)))))) ∧ (p1 ∧ (p2 ∧ True))) ∨ (True → (p1 ∨ True))) ∨ p4) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135088587174366794711341746406 : ((((p3 ∨ (p4 ∧ (((p3 ∨ True) → p2) ∧ (True → (False → True))))) → (p1 → (p5 ∧ (p1 ∧ p2)))) ∨ (p4 → p4)) ∨ ((p3 → True) ∧ True)) := by
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
theorem thm_5_vars_234751060846473797771126463309 : ((p4 → (p2 → p1)) → ((((p1 ∧ True) ∨ False) ∧ (((True → (p1 ∧ p4)) ∧ (p3 → (p1 → p1))) → (True ∧ ((p1 ∧ p3) ∨ True)))) → p1)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160546795461615238779024965253 : (((p3 ∨ (True → (((p5 → p3) ∨ (True ∨ (p5 ∨ p4))) → p5))) ∨ (p3 → (False → (False ∨ p1)))) → (((p3 → (p1 ∧ p5)) → p2) ∨ True)) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_105914145928865235260355414745 : (((((p4 → False) → (False ∧ (True ∧ (p5 ∨ (p3 ∧ (p2 ∧ False)))))) ∧ p2) ∨ (((p2 ∧ (p4 ∧ (p4 ∨ p5))) → p5) ∨ True)) ∧ (p1 → p1)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124267083388987048792379817329 : (((p3 ∨ (False → ((((p1 ∧ p1) ∧ p3) ∨ p5) ∧ p2))) → (((p3 ∨ False) → p4) ∧ (False ∧ (p3 → (p5 ∧ (False → False)))))) → (p5 ∧ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 ∨ (False → ((((p1 ∧ p1) ∧ p3) ∨ p5) ∧ p2))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : (p3 ∨ (False → ((((p1 ∧ p1) ∧ p3) ∨ p5) ∧ p2))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h8
    -- False on the left can always be used.
    apply False.elim h8
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h7
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153240401666139893286507489049 : ((False ∨ ((p4 ∧ (((p3 → False) ∨ ((((True ∧ True) ∧ p5) ∧ p5) ∧ ((False ∧ p4) ∧ False))) → p1)) ∧ p4)) → ((p3 → (False ∨ p1)) ∨ p4)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134458601055153123200500838132 : (((((p4 ∨ ((False ∧ (p1 → True)) ∨ True)) ∧ ((((True ∨ False) ∨ p3) → True) ∧ (p2 ∨ (p1 ∧ p5)))) ∧ p3) → p4) ∨ (True ∨ (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777210164948135920700892913650 : (((p1 ∨ (((p5 ∧ ((((p2 ∧ (p1 ∧ ((p3 ∨ False) → False))) ∨ p1) ∨ True) ∨ ((p1 ∧ True) ∧ p1))) ∧ True) ∨ (p5 ∨ (False → p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689921229738289148633105684493 : (((((p1 → p4) → ((p2 ∨ ((p1 ∨ (p2 ∨ True)) ∨ p2)) → (p2 → (p5 ∨ p2)))) ∨ ((False ∧ p3) ∨ (p4 → ((True ∧ True) ∨ False)))) ∨ False) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64372661301431458158538327862 : ((p1 ∨ (((True ∧ p4) → (((((True ∧ p4) → (p1 ∧ (False ∨ (False ∨ p5)))) → p1) → p5) ∧ ((p5 ∧ p5) → (True → p3)))) ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52791927179570246353376110060 : (((((((True ∨ p2) ∨ (False ∧ p5)) → False) ∧ p5) ∧ ((p5 → p5) → True)) → (((True ∧ p2) ∧ ((p4 → p5) ∨ (p1 ∧ p4))) ∨ False)) ∨ p3) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : ((True ∨ p2) ∨ (False ∧ p5)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199582424848908455806707162670 : ((((p1 → ((False → p5) ∨ False)) ∨ p1) → p4) → ((((True ∨ (True ∨ p1)) → p5) ∧ ((p5 ∧ p4) ∧ False)) ∨ (p4 ∨ (p3 ∨ (p2 ∧ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p1 → ((False → p5) ∨ False)) ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174793324804840186130634923812 : (((p3 ∨ p5) ∧ ((((p3 ∨ p1) ∨ p1) ∨ (False ∨ (True ∨ (p2 → True)))) ∧ p1)) → (p1 ∧ ((False ∧ False) ∨ ((p1 ∧ (p2 ∧ False)) → p4)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- One of the premise coincides with the conclusion.
          exact h6
        case inr h10 =>
          -- One of the premise coincides with the conclusion.
          exact h6
      case inr h11 =>
        -- One of the premise coincides with the conclusion.
        exact h6
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- False on the left can always be used.
        apply False.elim h13
      case inr h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- One of the premise coincides with the conclusion.
          exact h6
        case inr h16 =>
          -- One of the premise coincides with the conclusion.
          exact h6
  case inr h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h3.left
    let h19 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h21 =>
        -- Disjunctions on the left can always be decomposed.
        cases h21
        case inl h22 =>
          -- One of the premise coincides with the conclusion.
          exact h19
        case inr h23 =>
          -- One of the premise coincides with the conclusion.
          exact h19
      case inr h24 =>
        -- One of the premise coincides with the conclusion.
        exact h19
    case inr h25 =>
      -- Disjunctions on the left can always be decomposed.
      cases h25
      case inl h26 =>
        -- False on the left can always be used.
        apply False.elim h26
      case inr h27 =>
        -- Disjunctions on the left can always be decomposed.
        cases h27
        case inl h28 =>
          -- One of the premise coincides with the conclusion.
          exact h19
        case inr h29 =>
          -- One of the premise coincides with the conclusion.
          exact h19
  -- Conjunctions on the left can always be decomposed.
  let h30 := h1.left
  let h31 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h30
  case inl h32 =>
    -- Conjunctions on the left can always be decomposed.
    let h33 := h31.left
    let h34 := h31.right
    -- Disjunctions on the left can always be decomposed.
    cases h33
    case inl h35 =>
      -- Disjunctions on the left can always be decomposed.
      cases h35
      case inl h36 =>
        -- Disjunctions on the left can always be decomposed.
        cases h36
        case inl h37 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h38
          -- Conjunctions on the left can always be decomposed.
          let h39 := h38.left
          let h40 := h38.right
          -- Conjunctions on the left can always be decomposed.
          let h41 := h40.left
          let h42 := h40.right
          -- False on the left can always be used.
          apply False.elim h42
        case inr h43 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h44
          -- Conjunctions on the left can always be decomposed.
          let h45 := h44.left
          let h46 := h44.right
          -- Conjunctions on the left can always be decomposed.
          let h47 := h46.left
          let h48 := h46.right
          -- False on the left can always be used.
          apply False.elim h48
      case inr h49 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h50
        -- Conjunctions on the left can always be decomposed.
        let h51 := h50.left
        let h52 := h50.right
        -- Conjunctions on the left can always be decomposed.
        let h53 := h52.left
        let h54 := h52.right
        -- False on the left can always be used.
        apply False.elim h54
    case inr h55 =>
      -- Disjunctions on the left can always be decomposed.
      cases h55
      case inl h56 =>
        -- False on the left can always be used.
        apply False.elim h56
      case inr h57 =>
        -- Disjunctions on the left can always be decomposed.
        cases h57
        case inl h58 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h59
          -- Conjunctions on the left can always be decomposed.
          let h60 := h59.left
          let h61 := h59.right
          -- Conjunctions on the left can always be decomposed.
          let h62 := h61.left
          let h63 := h61.right
          -- False on the left can always be used.
          apply False.elim h63
        case inr h64 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h65
          -- Conjunctions on the left can always be decomposed.
          let h66 := h65.left
          let h67 := h65.right
          -- Conjunctions on the left can always be decomposed.
          let h68 := h67.left
          let h69 := h67.right
          -- False on the left can always be used.
          apply False.elim h69
  case inr h70 =>
    -- Conjunctions on the left can always be decomposed.
    let h71 := h31.left
    let h72 := h31.right
    -- Disjunctions on the left can always be decomposed.
    cases h71
    case inl h73 =>
      -- Disjunctions on the left can always be decomposed.
      cases h73
      case inl h74 =>
        -- Disjunctions on the left can always be decomposed.
        cases h74
        case inl h75 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h76
          -- Conjunctions on the left can always be decomposed.
          let h77 := h76.left
          let h78 := h76.right
          -- Conjunctions on the left can always be decomposed.
          let h79 := h78.left
          let h80 := h78.right
          -- False on the left can always be used.
          apply False.elim h80
        case inr h81 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h82
          -- Conjunctions on the left can always be decomposed.
          let h83 := h82.left
          let h84 := h82.right
          -- Conjunctions on the left can always be decomposed.
          let h85 := h84.left
          let h86 := h84.right
          -- False on the left can always be used.
          apply False.elim h86
      case inr h87 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h88
        -- Conjunctions on the left can always be decomposed.
        let h89 := h88.left
        let h90 := h88.right
        -- Conjunctions on the left can always be decomposed.
        let h91 := h90.left
        let h92 := h90.right
        -- False on the left can always be used.
        apply False.elim h92
    case inr h93 =>
      -- Disjunctions on the left can always be decomposed.
      cases h93
      case inl h94 =>
        -- False on the left can always be used.
        apply False.elim h94
      case inr h95 =>
        -- Disjunctions on the left can always be decomposed.
        cases h95
        case inl h96 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h97
          -- Conjunctions on the left can always be decomposed.
          let h98 := h97.left
          let h99 := h97.right
          -- Conjunctions on the left can always be decomposed.
          let h100 := h99.left
          let h101 := h99.right
          -- False on the left can always be used.
          apply False.elim h101
        case inr h102 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h103
          -- Conjunctions on the left can always be decomposed.
          let h104 := h103.left
          let h105 := h103.right
          -- Conjunctions on the left can always be decomposed.
          let h106 := h105.left
          let h107 := h105.right
          -- False on the left can always be used.
          apply False.elim h107



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_767788609571471936803236396963 : (((p5 ∧ (((((p3 → (p5 ∨ ((((p1 ∨ (True ∧ (False ∨ p4))) ∨ False) → p3) ∧ p5))) ∧ (p4 → True)) ∨ (p5 ∧ p3)) → p5) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115874262161314760037287724475 : (((((p3 ∧ p4) → p3) ∧ False) ∨ (p4 ∨ ((p1 → (((p2 ∨ ((False → True) ∧ (False ∧ (p5 ∨ p3)))) ∨ p1) ∧ False)) ∧ p3))) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193169761544133767667845648494 : ((((p5 ∧ (p4 → p5)) ∧ True) → ((p1 ∧ p3) ∧ False)) → ((True ∧ p5) → (p2 ∨ (p4 ∧ (True ∨ (((p5 ∧ (p5 ∧ p3)) → p3) ∨ p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : ((p5 ∧ (p4 → p5)) ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h4
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h5
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53772803191623434389309030753 : (((((p3 ∧ (p4 → ((p4 ∨ True) ∧ True))) → p4) ∨ p3) ∨ ((False → ((False ∧ (p4 ∨ p5)) → False)) ∨ ((p4 → (True → p2)) ∧ p5))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608598530225829243603763483601 : (((((((((((True ∨ (True ∨ p1)) ∧ (False ∨ (p5 → (p5 ∧ True)))) → p1) ∧ p3) ∧ p2) ∧ (p1 ∨ p3)) ∧ (p3 → p5)) ∨ True) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_707867862284091751155172703752 : ((((p3 ∧ ((p2 → ((p1 ∧ p5) ∨ p5)) ∨ True)) ∨ (((True → p3) ∨ p3) → ((p1 ∧ ((p2 → (True ∨ p1)) ∧ (p2 ∨ p4))) ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_742376080622442624473177309765 : ((((p1 → p4) ∨ (((p2 ∨ False) ∨ (((p5 ∧ (p3 ∨ p2)) ∨ p1) → False)) ∨ ((p2 ∨ ((p5 ∨ True) ∨ (p2 → (p4 ∨ p3)))) ∨ p1))) ∨ False) ∧ True) := by
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
theorem thm_5_vars_742866219038133581079173221247 : ((((p3 → p2) ∨ (p2 → ((((True ∧ (False → (True ∨ p4))) ∨ (p5 ∨ p4)) → p4) ∨ (((p1 → p5) → ((p3 → p3) ∨ p3)) ∨ p4)))) ∨ p2) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137483234856756317000115279391 : ((p5 ∧ ((p5 ∨ (((p1 → p4) ∧ (p4 ∧ p4)) ∧ ((((False ∧ p5) ∨ p4) ∧ ((True → True) ∨ p3)) → p5))) ∧ p1)) ∨ ((p4 ∧ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45788572708363620180326495739 : (((p1 → (((((p5 ∧ p1) ∧ (True → ((p2 → p4) ∧ ((p2 → p4) ∨ False)))) ∧ ((p1 ∧ p2) ∨ p5)) ∨ p3) ∨ (p4 ∧ p2))) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191992898081210770420828677311 : ((p1 → ((((p3 → (p1 ∨ p4)) ∧ p4) ∧ p2) → False)) ∨ ((((p1 → p4) ∧ (True → (((False ∧ (p4 ∧ p2)) ∧ p1) ∨ False))) ∧ p2) → p4)) := by
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
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
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
    apply False.elim h11
  case inr h13 =>
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264397297266425279179006084476 : (True ∧ (((True → p5) ∨ (p4 → p2)) ∨ (p2 → (((p3 ∧ (p3 ∨ (False ∨ (False ∨ ((p3 → p2) ∨ True))))) ∧ (p5 → (p4 ∧ True))) ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246054922009871127701792927191 : ((p4 ∧ False) ∨ (p1 ∨ (((p3 ∨ (p1 ∧ False)) ∧ p5) ∨ (p5 ∨ ((((True ∨ False) ∧ True) → p2) → (((p4 → p2) ∨ (True ∨ p5)) ∨ p4)))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197442268687615786513441111013 : ((((p5 → (p4 → p1)) ∧ p5) ∧ (p1 → p2)) ∨ ((False ∨ (p5 ∧ ((p5 ∨ (True ∨ p5)) ∧ (True ∧ ((True ∨ p5) ∧ (False ∧ p5)))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51266422811762748996563293952 : ((((p1 ∨ p5) → (((p2 ∧ False) ∧ (False → (False ∨ True))) ∨ (((p2 ∨ True) ∨ p5) ∧ p4))) ∨ (((p1 ∧ (False ∧ p1)) ∨ p5) → p5)) ∨ p3) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328270978519104438245617202321 : (True → ((((p5 ∨ ((p2 ∨ True) ∧ (p3 ∧ ((p5 → p1) ∨ p3)))) ∨ (False ∨ (p5 → (p5 → p3)))) ∧ False) ∨ (((p1 ∧ p2) ∨ p4) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160362195815353353081417732796 : (((((p3 ∧ (p4 → False)) ∨ ((True ∧ (p3 → p5)) ∨ (True ∨ False))) → p4) ∧ (p2 → (p1 ∧ p3))) → ((((False ∧ p5) → p4) ∧ p4) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p3 ∧ (p4 → False)) ∨ ((True ∧ (p3 → p5)) ∨ (True ∨ False))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- False on the left can always be used.
  apply False.elim h7
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171838128541221276006434224257 : ((((p1 ∧ (p2 ∧ p3)) → (((p5 → p1) ∨ True) ∨ ((True ∨ p2) ∨ p5))) → p1) ∨ (p1 → ((p2 ∧ p1) ∨ ((False ∧ p5) ∨ (p5 → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680384277632959044144003291539 : (((((p4 ∨ (p3 ∨ (((p1 → (False ∧ False)) ∧ p3) ∨ (p5 ∧ (p1 → p1))))) → ((p1 ∧ p4) ∨ p1)) → ((p4 ∨ (True → p1)) → p1)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h4 : (p4 ∨ (p3 ∨ (((p1 → (False ∧ False)) ∧ p3) ∨ (p5 ∧ (p1 → p1))))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h5 := h1 h4
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h9
  case inr h10 =>
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h11 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h12 := h10 h11
    -- One of the premise coincides with the conclusion.
    exact h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52224883971494219392696600248 : (((True ∧ (p2 ∧ (((p3 ∨ p1) → (((True ∧ False) ∨ (p1 → p4)) → p3)) ∧ p4))) → ((True → False) → (False ∨ (False ∧ (p2 → True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207399080379193556046899418338 : (((p3 ∧ ((False ∧ p2) → True)) ∨ p3) → (((p2 → p5) → ((p1 → ((p1 → False) ∧ p1)) → (p3 → (False ∨ p1)))) ∨ ((False ∧ True) → p2))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618584115749983324700306785314 : (((((p3 ∨ (False ∧ (p3 ∧ p1))) → (p4 ∨ (((((p3 ∧ p2) → p4) ∧ (p4 ∧ p4)) → False) ∧ ((p3 ∨ p3) → (False ∨ p1))))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_337691352819123269693380732380 : (p1 → (((((True ∧ (((p4 → p3) ∧ p1) → False)) ∨ (p1 ∧ ((True ∨ p3) ∧ False))) → p4) → False) → ((p1 → (p4 ∧ p2)) → (False ∧ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (((True ∧ (((p4 → p3) ∧ p1) → False)) ∨ (p1 ∧ ((True ∨ p3) ∧ False))) → p4) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h9 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h1
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h10 := h3 h9
      -- We need to get the left conjuct of h10 based on <expert-advice>.
      let h11 := h10.left
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h17 =>
        -- False on the left can always be used.
        apply False.elim h16
      case inr h18 =>
        -- False on the left can always be used.
        apply False.elim h16
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h19 := h2 h4
  -- False on the left can always be used.
  apply False.elim h19
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h20 : (((True ∧ (((p4 → p3) ∧ p1) → False)) ∨ (p1 ∧ ((True ∨ p3) ∧ False))) → p4) := by
    -- Implications on the right can always be decomposed.
    intro h21
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h22.left
      let h24 := h22.right
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h25 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h1
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h26 := h3 h25
      -- We need to get the left conjuct of h26 based on <expert-advice>.
      let h27 := h26.left
      -- One of the premise coincides with the conclusion.
      exact h27
    case inr h28 =>
      -- Conjunctions on the left can always be decomposed.
      let h29 := h28.left
      let h30 := h28.right
      -- Conjunctions on the left can always be decomposed.
      let h31 := h30.left
      let h32 := h30.right
      -- Disjunctions on the left can always be decomposed.
      cases h31
      case inl h33 =>
        -- False on the left can always be used.
        apply False.elim h32
      case inr h34 =>
        -- False on the left can always be used.
        apply False.elim h32
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h35 := h2 h20
  -- False on the left can always be used.
  apply False.elim h35



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179215588767220464673918044383 : ((p4 ∧ (((p1 → ((p3 ∧ True) ∨ False)) ∨ (p1 ∨ True)) → (p5 ∧ p1))) ∨ (((p5 → (p3 ∧ (False → (p1 ∨ p3)))) → (p3 ∧ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



