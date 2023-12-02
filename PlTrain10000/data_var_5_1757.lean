variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43750216189317193762785183640 : ((((True ∧ (True → ((p3 ∧ (p3 ∨ (p4 ∧ ((True → (False → p4)) ∧ ((p2 ∨ False) ∨ ((p2 ∧ p3) ∨ False)))))) ∨ p4))) → False) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_162898415204647418409177523007 : (((p3 → (((p1 → False) ∨ ((p3 ∧ (False ∨ (p3 ∨ p3))) ∧ p3)) ∨ True)) ∨ (p2 ∧ False)) ∧ (p2 → ((((p5 → False) ∨ p5) ∨ False) ∨ p2))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192297863343403331366700312794 : ((((p2 → p1) → (p4 → (p1 ∨ (p5 → False)))) ∧ p2) → (p5 ∨ ((p3 ∨ (((((p4 ∧ p5) ∧ p5) ∧ p3) ∧ p2) ∨ p4)) ∨ (p1 → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234122343303745796593758681037 : ((True → (p2 ∨ p2)) → (((p4 ∧ (False ∨ False)) ∨ p2) ∨ ((((False ∧ (p4 → (False ∧ p4))) → ((p1 ∨ (False ∧ False)) → p4)) → p3) ∨ False))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190100304061340226542480663319 : (((((p1 ∨ (p1 → p1)) ∧ p3) → (p2 ∨ p4)) ∧ p1) ∨ ((((p2 → ((False ∧ (p2 → p3)) ∨ False)) ∨ False) ∨ ((p3 ∧ False) → p1)) ∨ False)) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62562558379437567965979092054 : ((p3 ∧ (p5 ∨ ((p4 → ((p5 → ((p1 ∨ (True → ((p5 ∧ (((p3 ∧ p2) ∧ True) ∧ False)) → False))) → False)) ∧ True)) → (p1 ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328422317454490017491984700871 : (True → (((p5 ∧ (p4 → True)) ∨ (p3 → ((p5 → (False ∧ (((p4 → p3) ∨ p2) → p2))) ∨ p2))) ∨ (p5 ∨ (p3 ∨ (p3 → (True ∨ p1)))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689236337601802957875045134333 : (((((p2 ∧ ((((p5 → p5) → ((p2 → False) ∨ p3)) → True) ∧ (True → True))) → p5) ∨ (True → (((True ∧ p1) → p2) → (False → p2)))) ∨ False) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148922669557565251814550855005 : ((((p1 ∧ (p4 → False)) → p5) → (p5 ∨ ((p2 ∧ p4) ∧ ((((p4 ∧ True) ∨ p4) ∨ (p4 → p2)) → p2)))) ∨ ((p2 → p4) ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198517003806668044019301029670 : ((False ∨ ((p5 ∧ (True → (p5 ∧ p3))) ∧ False)) ∨ (p2 ∨ ((p3 ∨ ((p1 ∧ (p1 ∧ ((p2 ∧ p4) → ((p5 ∨ p1) → True)))) ∧ p1)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161192478692067444275761910831 : (((p3 ∨ p5) ∨ (((p2 ∨ p4) ∧ ((p4 → p1) ∧ p2)) → (((p1 ∨ p2) → (p5 ∨ p5)) → p4))) → (((p2 ∧ p3) ∧ p5) ∨ (p5 ∨ True))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133765246006267250968525948841 : (((((True → p2) ∨ ((True → False) → p4)) → (((p1 ∧ ((False → (p3 ∨ p2)) ∨ p2)) ∨ (p3 ∧ p2)) ∨ p1)) ∧ True) ∨ (p3 → (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325084528417429765707694438490 : (p5 ∨ ((True → p5) → ((((p5 ∨ ((p5 → ((p4 → (p3 ∧ p1)) ∨ p1)) ∨ (p4 ∨ False))) ∧ (p5 ∨ p4)) ∨ ((p1 ∧ p3) ∧ p1)) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247423309503777264878730366634 : ((False ∨ p2) ∨ ((p2 ∧ (((True → p1) → ((True ∨ (True ∨ (p2 → ((True ∧ True) ∧ p1)))) ∧ (False ∧ p3))) ∨ True)) ∨ (p3 ∨ (p4 → p4)))) := by
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
theorem thm_5_vars_171679588604147082058216649978 : (((p2 ∨ ((p1 ∨ ((((p4 ∨ (False → True)) ∧ p1) ∨ p1) ∨ p5)) ∧ True)) ∨ p1) ∨ (((p3 ∨ False) → (True ∧ (p4 ∨ (True → p3)))) ∨ False)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303033346774808639998936216358 : (False ∨ (p1 → (p2 → ((((p3 → ((p2 ∧ p1) → p2)) ∧ p2) ∨ p4) → ((((False ∧ p2) ∧ (p4 ∧ (p5 ∧ p1))) ∨ p1) ∨ (p5 ∨ p5)))))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256911385225287607206983073076 : ((p1 ∨ p4) → (((p5 ∧ p1) ∧ True) ∨ (p2 ∨ (((p5 ∧ (False ∨ p4)) ∧ p3) → ((p1 ∨ ((p2 → True) ∧ p3)) → (p4 → (p4 ∨ p5))))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h3.left
      let h8 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h7.left
      let h10 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- False on the left can always be used.
        apply False.elim h11
      case inr h12 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h12
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Conjunctions on the left can always be decomposed.
      let h16 := h3.left
      let h17 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h18 := h16.left
      let h19 := h16.right
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h20 =>
        -- False on the left can always be used.
        apply False.elim h20
      case inr h21 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h21
  case inr h22 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h23
    -- Implications on the right can always be decomposed.
    intro h24
    -- Implications on the right can always be decomposed.
    intro h25
    -- Disjunctions on the left can always be decomposed.
    cases h24
    case inl h26 =>
      -- Conjunctions on the left can always be decomposed.
      let h27 := h23.left
      let h28 := h23.right
      -- Conjunctions on the left can always be decomposed.
      let h29 := h27.left
      let h30 := h27.right
      -- Disjunctions on the left can always be decomposed.
      cases h30
      case inl h31 =>
        -- False on the left can always be used.
        apply False.elim h31
      case inr h32 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h32
    case inr h33 =>
      -- Conjunctions on the left can always be decomposed.
      let h34 := h33.left
      let h35 := h33.right
      -- Conjunctions on the left can always be decomposed.
      let h36 := h23.left
      let h37 := h23.right
      -- Conjunctions on the left can always be decomposed.
      let h38 := h36.left
      let h39 := h36.right
      -- Disjunctions on the left can always be decomposed.
      cases h39
      case inl h40 =>
        -- False on the left can always be used.
        apply False.elim h40
      case inr h41 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h41



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51158123699587878459738577983 : ((((False → ((p3 → (((False ∧ p2) ∧ (p2 ∧ (p3 ∧ (p2 ∧ p3)))) ∧ p4)) ∨ p2)) → p4) ∨ (p1 ∨ ((True → p2) ∨ (p4 ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64550299846703314579099770725 : ((p1 ∨ (((p2 ∧ p1) → (False ∧ p3)) ∧ ((p2 ∧ p2) ∧ (((p1 → ((p1 ∨ (p4 → (p1 ∧ p3))) ∨ (True ∧ p5))) ∨ p4) → p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311827744108102840974212301466 : (p2 ∨ (p1 ∨ (((p4 ∨ (((p2 ∧ (p5 ∧ p3)) ∧ p4) ∧ p3)) → p1) → (((p4 ∨ p5) ∧ ((False ∧ ((True ∨ p5) ∧ p1)) ∧ p5)) ∨ True)))) := by
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
theorem thm_5_vars_719165953781012725820905839123 : ((((p1 ∧ (p2 → (p4 ∧ p5))) ∨ (True → (p4 → (p3 → ((p4 ∨ (False → ((p5 ∨ ((p2 → (p5 → False)) ∨ p4)) ∧ p5))) → p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684372880756949512528918386806 : ((((((True ∧ p4) ∨ (((p5 → p4) ∨ (True → p5)) → False)) ∨ (p4 → ((False ∧ True) ∧ False))) ∨ (p5 → ((p2 ∨ p5) ∨ (p5 ∨ p3)))) ∨ p4) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52830565345050092691945361905 : (((((p3 ∨ p5) → p5) ∨ ((((True → p4) → (p3 → p5)) ∨ p2) → True)) → ((True → (p4 → (((True → p2) ∨ p5) ∨ True))) ∨ p3)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_83127634895884282296543076790 : (((False ∨ ((((True ∨ p4) → ((p2 ∨ False) ∨ True)) ∧ ((False → p5) ∨ (p3 ∧ p5))) ∧ (p2 ∨ True))) → (p5 ∧ (p5 ∧ (p5 ∧ False)))) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False ∨ ((((True ∨ p4) → ((p2 ∨ False) ∨ True)) ∧ ((False → p5) ∨ (p3 ∧ p5))) ∧ (p2 ∨ True))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h3
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h2
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206072978489876773704759367747 : ((p3 ∧ ((p4 → (p5 ∨ p5)) → False)) ∨ (((((p1 ∨ False) ∨ p4) ∨ (p5 ∧ p1)) ∨ ((p1 ∧ (((p3 ∧ p2) → p1) → True)) → True)) ∨ p2)) := by
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
theorem thm_5_vars_585372131024367868029055441444 : ((((((((((p2 ∨ p1) ∧ (p5 ∨ (False → p5))) → True) → False) ∨ (p4 → (False ∧ ((p1 ∧ (True ∧ p1)) → p1)))) ∧ p3) ∧ p1) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257074829444933166207607760906 : ((p2 ∨ False) → ((((((p5 ∧ p5) → (p1 ∨ p3)) → (p3 → ((p1 ∧ p3) ∧ p5))) ∨ (p1 → ((p2 ∧ False) → p2))) ∨ p4) ∨ (p5 → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49230883508268899061831025729 : ((((p5 ∨ False) ∨ ((p1 ∧ (p4 ∨ True)) ∨ ((p5 ∧ ((p3 ∨ p5) ∧ (p3 ∧ (True → p5)))) → (p1 ∧ p4)))) ∨ (p5 ∨ (False → True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320088025185440105809824550466 : (p4 ∨ (((p1 ∧ p4) ∨ p3) → (((p5 → (p4 ∨ (((p5 → p5) → False) ∧ (p1 ∨ (p5 ∨ p4))))) ∧ (p4 → (True ∧ (p1 → p2)))) ∨ True))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47168817016938813356322414791 : (((((((p3 ∨ True) ∧ ((p1 ∨ p3) ∨ False)) ∨ ((True → p1) ∧ True)) ∧ False) ∨ ((p3 ∨ p1) → ((p5 ∨ False) ∨ False))) ∨ (p1 → True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_632795342401987622388797676858 : ((((((((p1 ∨ False) ∧ ((((p4 ∧ (p5 → (((p5 → True) → True) ∧ p3))) ∧ p1) ∨ p4) ∨ p2)) → p5) ∨ p1) ∧ (True ∧ True)) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41935943109482450554326196746 : ((((p2 → (True → p1)) → ((p1 → p5) → ((p2 ∨ True) ∧ (((p2 ∨ p3) ∨ (True ∧ (p1 → p3))) ∨ (True ∨ (p5 ∧ p1)))))) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186281173645432562791868597749 : ((((((True ∧ (p5 → p4)) ∧ (False → p1)) ∧ p4) → False) → p3) → (((False → (p3 ∨ (p1 ∧ p2))) ∧ ((p4 ∨ p3) → p5)) ∨ (p1 → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159311667544482035965671128688 : ((p5 → ((p4 ∨ ((p1 ∧ (p5 ∧ (p3 ∨ p2))) → (p5 ∧ ((True ∧ (p3 → False)) ∧ p3)))) → p3)) ∨ (False → (((True ∨ p3) ∧ False) → p1))) := by
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
    apply False.elim h4
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113191618415096019517876674748 : ((((False ∧ (((((p1 ∧ (p3 → False)) ∨ (p1 ∧ p4)) ∧ True) ∧ ((p2 → p1) ∨ p2)) → (False ∨ p2))) ∧ False) ∧ (p2 ∧ True)) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_132696439185004593175377415448 : ((False ∨ ((p4 ∧ p3) → (((p4 ∧ (((p3 → p3) ∨ True) ∨ ((p2 → p2) ∧ p1))) → p1) ∨ ((p2 ∨ p3) ∨ p1)))) ∧ ((p5 ∨ p5) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48802078433156107633743453284 : (((p1 ∧ (False ∧ (((p4 → ((p5 ∨ p4) → (p4 → ((p5 ∧ (p1 ∨ False)) ∨ p5)))) ∨ p2) ∨ (p4 ∧ p2)))) ∧ (True ∧ (p2 → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250884522933544000200447617866 : ((p1 → p3) ∨ ((((p5 → p1) ∨ (((p3 → (p3 ∨ p1)) ∨ p1) → (((p4 ∧ p2) ∨ p4) ∧ False))) ∨ (False ∨ True)) ∨ ((p2 → p3) → p2))) := by
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
theorem thm_5_vars_261178985770054667034226385127 : ((p4 → p4) → (p4 ∨ (((((p1 ∨ (p1 ∧ p5)) ∨ False) → p3) ∧ p5) → ((False → (p5 ∧ (p2 ∨ True))) → (((p5 ∧ p5) → p3) → p3))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h7 : (p5 ∧ p5) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h6
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h8 := h4 h7
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337708337113046650390175030495 : (p1 → (((p4 ∨ p3) ∨ (((((p1 ∨ p2) ∧ p5) ∧ p5) ∧ (p2 ∨ p3)) ∧ ((p5 ∨ p2) → False))) → ((p2 ∨ p5) ∨ ((p3 ∨ p4) → True)))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h11.left
    let h14 := h11.right
    -- Conjunctions on the left can always be decomposed.
    let h15 := h13.left
    let h16 := h13.right
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h18 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h18
      case inr h19 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h14
    case inr h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h21 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h21
      case inr h22 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337645943363531509237668970504 : (p1 → ((((((p4 → (p2 → False)) → ((True ∨ ((p1 ∨ p4) ∧ False)) ∧ p2)) ∨ True) ∧ p3) ∧ p4) ∨ (p1 → (True ∨ ((True ∨ p1) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251127451955475895651949631891 : ((p2 → False) ∨ ((((p3 → ((p5 ∧ p3) ∨ ((p1 → ((p4 → p4) → p2)) ∧ (True ∧ p3)))) ∧ p1) → (p5 ∧ p3)) ∨ (p3 → (False ∨ True)))) := by
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
theorem thm_5_vars_149922619914939204550929530854 : ((p3 ∨ (((((p2 → p3) → False) ∧ (((True → (p1 ∧ p4)) ∧ p5) ∧ p2)) ∧ p1) ∧ (p3 ∧ (True → True)))) ∨ ((p3 ∨ (p3 ∧ p4)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655582260175511706853561004315 : (((((((False ∨ p4) → p1) → (((True → True) → (p3 ∧ p3)) ∨ ((p5 ∧ p2) → (p5 ∨ (p5 ∧ p2))))) → (False ∧ p5)) ∨ (False → p1)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_115884300156613081092007425158 : (((((False ∧ p1) ∨ False) ∨ p3) ∨ (((True ∨ ((((p4 ∧ p4) → (p5 ∨ ((p4 ∧ p3) ∨ p4))) ∨ True) ∧ True)) ∧ p2) → p3)) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51113084177463834662812543094 : (((((((p4 → (((True ∧ p1) → p5) ∨ False)) ∨ (p4 ∨ False)) → (True ∧ p2)) ∨ p1) ∨ p3) ∨ ((p2 → ((False → p3) → True)) ∨ p5)) ∨ p2) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50673627490687454913763769612 : ((((p5 ∧ ((True → p5) → (True → p4))) → ((((p1 ∧ p2) ∧ False) ∧ True) ∧ (p3 ∧ (p2 ∧ p4)))) → ((p1 ∨ p1) ∨ (p2 → p2))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_605216807598374110335612849307 : ((((p2 → (False ∧ ((p5 ∨ (((p2 → p3) ∨ (p4 ∨ (True ∨ p2))) → (p3 ∨ p3))) ∧ ((p2 ∨ ((p4 ∧ p2) → p1)) ∧ False)))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323350584711607261397031567262 : (p5 ∨ (((((p5 → p5) → False) ∧ p5) ∨ ((p4 ∨ ((p3 ∨ p4) ∨ (p1 ∨ ((p3 → p3) ∨ (p2 ∨ p2))))) → (False ∧ p4))) → (p5 ∨ p4))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : (p4 ∨ ((p3 ∨ p4) ∨ (p1 ∨ ((p3 → p3) ∨ (p2 ∨ p2))))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h7
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h6
    -- We need to get the left conjuct of h8 based on <expert-advice>.
    let h9 := h8.left
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137688323908032180538014795660 : ((p1 ∨ ((p4 → (((p5 ∧ True) ∧ ((True ∨ p1) ∨ ((((p5 ∨ (p1 ∨ p2)) → False) ∧ p3) ∨ p5))) ∨ p1)) ∨ True)) ∨ (p5 ∨ (p4 ∨ p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302811685996777150683030144881 : (False ∨ (p5 ∨ ((((False ∨ ((p2 → (((p2 ∨ p3) ∨ p4) ∨ (False ∨ ((p3 ∧ p3) → True)))) ∧ (p4 → p2))) ∨ False) ∧ False) ∨ (p3 → p3)))) := by
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
theorem thm_5_vars_57895318452999708921240705208 : (((p3 ∨ (p2 ∨ False)) → (((((((p5 ∨ (p5 ∧ p1)) ∨ p1) → (p2 ∨ (p1 ∨ p3))) ∧ (p2 ∧ p5)) → (p1 ∧ p2)) ∨ p1) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205532389506366374930918091234 : (((p1 ∨ False) ∧ ((p4 → False) ∨ True)) ∨ (((p4 ∨ False) ∧ (((False → (p2 → True)) ∨ (True → p5)) ∨ p3)) ∨ (False → ((p3 ∧ p1) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114066604121166661515453461869 : ((((False ∨ (((True → p4) ∨ False) ∧ (p4 ∧ p5))) ∨ ((False → ((p3 ∨ p4) → p5)) → (True → False))) ∨ (p1 → (p3 → p1))) ∨ (p2 ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112986773462121994422689377718 : (((p2 ∧ (p2 ∨ (p1 ∨ ((((p2 ∧ p1) → (p1 ∨ False)) ∨ p5) ∨ ((False ∧ (False → p4)) ∨ (p3 ∧ (False ∧ False))))))) → False) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215713758432046457591019373579 : ((False ∨ (True ∧ (p5 ∨ p1))) ∨ (p3 ∨ ((((p5 ∨ True) ∧ p3) ∨ p5) → ((False ∧ p4) ∨ ((True ∧ ((p2 ∧ False) → p2)) ∧ (p4 ∨ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- False on the left can always be used.
      apply False.elim h8
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h10
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- False on the left can always be used.
      apply False.elim h12
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h14
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- False on the left can always be used.
    apply False.elim h16
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121743137733223855851909540775 : ((((((p3 ∨ p3) ∨ p5) ∨ True) ∧ (((p2 ∨ (p1 → p2)) ∧ (False ∧ (True → ((p1 ∨ (p4 ∧ p3)) ∧ p5)))) → p2)) → False) → (p3 ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p3 ∨ p3) ∨ p5) ∨ True) ∧ (((p2 ∨ (p1 → p2)) ∧ (False ∧ (True → ((p1 ∨ (p4 ∧ p3)) ∧ p5)))) → p2)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h5.left
      let h8 := h5.right
      -- False on the left can always be used.
      apply False.elim h7
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h5.left
      let h11 := h5.right
      -- False on the left can always be used.
      apply False.elim h10
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h12 := h1 h2
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_523277457869262276173369355889 : (((True ∧ ((p1 ∧ (((p1 ∨ p4) ∨ (p3 ∧ p2)) ∨ ((p1 ∧ ((((p4 ∧ ((p1 ∨ p4) → p5)) ∨ p2) ∧ p1) ∨ p4)) ∧ p5))) ∨ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702150710661248805255708854641 : ((((p5 → (((p5 → ((p1 ∧ True) → p1)) ∨ True) ∨ p1)) ∧ ((p3 ∧ p5) ∨ (((((False → (p5 ∨ p5)) → False) → p1) ∧ p4) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51171689809464143154649536185 : ((((((p2 ∨ p5) ∧ p1) ∧ (((p4 ∨ p5) → ((p1 → p5) → p3)) ∨ p4)) ∨ (p3 ∨ True)) ∨ (((p4 ∧ p4) ∧ (p1 ∨ p3)) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_163352261012914381336299951878 : ((((p3 ∧ (True → p3)) ∨ True) ∧ (p2 ∨ (((False → p5) ∨ (p5 → p1)) ∨ (p2 ∨ p1)))) ∧ ((((p2 → p5) ∨ False) → p2) ∨ (False → p3))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174575945635931210956842449334 : (((True → (p2 ∧ (False ∨ True))) ∧ ((p3 ∨ (p1 → ((p4 → p3) ∨ True))) → p4)) → (((p2 ∨ p3) → p4) ∨ (False ∨ (p1 ∨ (True ∧ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p3 ∨ (p1 → ((p4 → p3) ∨ True))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h7
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612520887548849727080305996785 : ((((((((p2 ∨ (p5 ∨ p5)) ∨ p1) ∨ ((p2 ∧ (True ∨ ((True ∨ p2) ∧ p4))) → ((p1 ∨ False) → p3))) ∨ False) ∨ (p5 ∧ p2)) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_198576446817757840312165841725 : ((p1 ∨ (p1 ∧ (((p2 ∧ p5) ∨ p3) ∧ p4))) ∨ (p4 ∨ (((((p3 → p4) ∨ (p4 → (p3 → p5))) ∧ p1) ∧ ((p1 ∧ True) ∨ p4)) → p1))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h10 =>
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h15 =>
      -- One of the premise coincides with the conclusion.
      exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180207245233603004989224446248 : ((((p3 ∨ p1) ∧ (p5 ∧ (True ∨ (((p3 ∨ True) → p4) ∧ p1)))) → True) → (p4 ∨ ((True ∧ p1) → ((p1 ∨ p2) ∧ ((p3 ∧ p4) → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62675621953773182449860604847 : ((p4 ∧ ((p3 ∧ ((((p3 ∨ p3) ∨ p3) ∨ False) ∧ (((p5 ∨ (False → p3)) → (((p5 ∨ (p1 ∨ True)) ∧ p3) ∧ p3)) ∨ p3))) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60595871291214267064719545946 : ((True ∧ ((p1 → (p5 ∧ (((((((p2 → (((p2 → p2) ∨ p5) ∨ False)) ∨ p2) ∨ p3) ∨ p4) ∨ p5) → p5) ∨ (p5 ∨ p5)))) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152770031637390693680759908598 : (((True ∧ True) → (((p2 ∨ p3) ∨ (p3 ∧ (p2 ∧ True))) ∧ ((p1 → ((p2 ∧ p5) → False)) ∨ (p5 ∨ p4)))) → ((p5 → p4) ∨ (False → False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134666636356552089669460386172 : ((((p3 ∨ (False → ((p3 ∧ ((False ∧ p2) ∧ p5)) → p4))) → (p4 → (((p2 ∨ False) ∨ True) → (p3 ∧ p3)))) → p5) ∨ (False → (p2 ∧ p2))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137360013364611280842386971483 : ((p3 ∧ ((((p1 → (((False → p1) ∧ (True → (p3 ∧ (True ∨ (False ∧ p5))))) ∧ True)) → p4) → (p4 ∧ p5)) → p3)) ∨ ((True ∨ p4) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165843698584918926357017191343 : ((((p4 ∨ p3) ∨ p3) ∨ ((p3 → p1) ∧ (((p4 ∨ p5) ∧ (p1 ∧ p4)) → (p3 ∧ False)))) ∨ (p3 → (True → (((False ∨ p4) ∨ True) ∨ p5)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110923388651096344552833352618 : ((((p2 → ((((False → (p1 → (p3 ∨ True))) ∧ True) ∧ ((p3 ∧ p2) ∧ (((p4 ∧ p1) → p5) ∨ False))) → p4)) → p2) ∧ p1) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53223528425357868834884331774 : ((((p5 ∧ (False → (p5 → p5))) ∧ ((p5 ∨ p2) ∧ (p4 ∨ p5))) ∨ ((((p5 ∨ ((False ∨ False) ∧ p4)) ∨ False) → p1) ∨ (p3 ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55807110682490230813662245480 : ((((p1 ∧ False) → (p4 ∨ p4)) ∧ ((((False → p4) → ((True ∧ True) → p4)) ∨ ((p5 ∨ (True ∧ p2)) → False)) → (False ∧ (p2 ∨ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158506766824341194632058151313 : (((True ∨ p5) → (False ∨ ((((p2 ∧ False) → p4) → ((p2 → p5) ∧ (p1 ∧ False))) → (True → p5)))) ∨ (((p1 ∨ (p3 ∨ p1)) ∨ False) ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : ((p2 ∧ False) → p4) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- False on the left can always be used.
      apply False.elim h8
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h9 := h3 h5
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h13
    -- Implications on the right can always be decomposed.
    intro h14
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58990741684319213880719339956 : (((p3 ∧ False) ∨ (((p1 ∨ p2) ∨ (((p1 ∧ (((True ∧ (p3 ∨ p2)) → (p2 → p3)) ∨ (False ∧ p3))) ∨ (p4 → p5)) ∧ p5)) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702226393380650026230753916435 : ((((((p5 ∧ (p3 ∧ (p4 ∨ p4))) ∧ (p4 ∨ p2)) ∧ False) ∨ (False → ((False ∨ ((p2 → p3) ∨ p3)) → ((p2 ∧ p2) ∨ (p3 ∨ False))))) ∨ p5) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h1
    case inr h6 =>
      -- False on the left can always be used.
      apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198388249601084759401731923408 : ((p3 ∧ ((p5 → p3) → (True → (p3 → p1)))) ∨ (p3 → (((p4 → (p5 ∨ (p1 ∨ p4))) → False) ∨ (((p3 ∨ False) ∨ True) ∨ (p1 → p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_41024195017927061337474798518 : (((((p4 → ((p1 ∧ (((p3 ∧ p3) ∨ (((True ∧ (p1 ∨ p2)) ∨ p2) → p2)) ∧ (p2 → p2))) ∨ p1)) → p3) → (p3 ∨ p2)) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186191681300325705059160898615 : (((True ∨ (((p2 ∨ p1) ∨ ((False ∧ True) → p3)) ∨ p2)) ∨ p1) → ((p4 ∧ (True → False)) → (p3 → (p3 ∧ (p4 ∧ ((p2 ∧ p4) ∧ p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Disjunctions on the left can always be decomposed.
          cases h10
          case inl h11 =>
            -- One of the premise coincides with the conclusion.
            exact h3
          case inr h12 =>
            -- One of the premise coincides with the conclusion.
            exact h3
        case inr h13 =>
          -- One of the premise coincides with the conclusion.
          exact h3
      case inr h14 =>
        -- One of the premise coincides with the conclusion.
        exact h3
  case inr h15 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h16 := h2.left
  let h17 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h18 =>
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h19 =>
      -- One of the premise coincides with the conclusion.
      exact h16
    case inr h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h21 =>
        -- Disjunctions on the left can always be decomposed.
        cases h21
        case inl h22 =>
          -- Disjunctions on the left can always be decomposed.
          cases h22
          case inl h23 =>
            -- One of the premise coincides with the conclusion.
            exact h16
          case inr h24 =>
            -- One of the premise coincides with the conclusion.
            exact h16
        case inr h25 =>
          -- One of the premise coincides with the conclusion.
          exact h16
      case inr h26 =>
        -- One of the premise coincides with the conclusion.
        exact h16
  case inr h27 =>
    -- One of the premise coincides with the conclusion.
    exact h16
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h28 := h2.left
  let h29 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h30 =>
    -- Disjunctions on the left can always be decomposed.
    cases h30
    case inl h31 =>
      -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
      have h32 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h29, we can now drive its conclusion.
      let h33 := h29 h32
      -- False on the left can always be used.
      apply False.elim h33
    case inr h34 =>
      -- Disjunctions on the left can always be decomposed.
      cases h34
      case inl h35 =>
        -- Disjunctions on the left can always be decomposed.
        cases h35
        case inl h36 =>
          -- Disjunctions on the left can always be decomposed.
          cases h36
          case inl h37 =>
            -- One of the premise coincides with the conclusion.
            exact h37
          case inr h38 =>
            -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
            have h39 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h29, we can now drive its conclusion.
            let h40 := h29 h39
            -- False on the left can always be used.
            apply False.elim h40
        case inr h41 =>
          -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
          have h42 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h29, we can now drive its conclusion.
          let h43 := h29 h42
          -- False on the left can always be used.
          apply False.elim h43
      case inr h44 =>
        -- One of the premise coincides with the conclusion.
        exact h44
  case inr h45 =>
    -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
    have h46 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h29, we can now drive its conclusion.
    let h47 := h29 h46
    -- False on the left can always be used.
    apply False.elim h47
  -- Conjunctions on the left can always be decomposed.
  let h48 := h2.left
  let h49 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h50 =>
    -- Disjunctions on the left can always be decomposed.
    cases h50
    case inl h51 =>
      -- One of the premise coincides with the conclusion.
      exact h48
    case inr h52 =>
      -- Disjunctions on the left can always be decomposed.
      cases h52
      case inl h53 =>
        -- Disjunctions on the left can always be decomposed.
        cases h53
        case inl h54 =>
          -- Disjunctions on the left can always be decomposed.
          cases h54
          case inl h55 =>
            -- One of the premise coincides with the conclusion.
            exact h48
          case inr h56 =>
            -- One of the premise coincides with the conclusion.
            exact h48
        case inr h57 =>
          -- One of the premise coincides with the conclusion.
          exact h48
      case inr h58 =>
        -- One of the premise coincides with the conclusion.
        exact h48
  case inr h59 =>
    -- One of the premise coincides with the conclusion.
    exact h48
  -- Conjunctions on the left can always be decomposed.
  let h60 := h2.left
  let h61 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h62 =>
    -- Disjunctions on the left can always be decomposed.
    cases h62
    case inl h63 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h64 =>
      -- Disjunctions on the left can always be decomposed.
      cases h64
      case inl h65 =>
        -- Disjunctions on the left can always be decomposed.
        cases h65
        case inl h66 =>
          -- Disjunctions on the left can always be decomposed.
          cases h66
          case inl h67 =>
            -- One of the premise coincides with the conclusion.
            exact h3
          case inr h68 =>
            -- One of the premise coincides with the conclusion.
            exact h3
        case inr h69 =>
          -- One of the premise coincides with the conclusion.
          exact h3
      case inr h70 =>
        -- One of the premise coincides with the conclusion.
        exact h3
  case inr h71 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_203810812050896932255889071034 : ((True → (p1 ∨ ((False → False) ∨ p2))) ∧ (((True → (p1 ∧ (p4 ∨ p3))) ∧ (p4 ∨ p4)) → ((p3 ∧ p2) ∨ (True ∨ ((False ∨ p2) ∧ p1))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
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
theorem thm_5_vars_178625992923192021590949151456 : ((((True ∨ (False → (True → False))) → p2) → (((p2 ∧ p1) ∨ p4) → False)) ∨ ((((p2 → False) → (True → p4)) → True) → ((True → False) → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44309743226571233954067981456 : (((((False → ((True → p3) ∨ (p3 → (((False ∧ p1) → (False → p3)) ∨ p3)))) ∨ p1) ∨ (p1 ∧ (p2 → ((False ∧ False) ∧ p5)))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613475575691622039399327177595 : (((((True → ((p4 ∨ p2) ∨ (((p3 ∧ p2) → p1) ∧ ((((p4 ∧ ((p3 ∨ False) ∧ p1)) → False) ∨ True) ∨ p4)))) → (p5 ∧ p1)) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_798306639295513394221549107811 : (((p1 → ((((p4 ∧ p2) ∧ True) → ((p4 → ((p4 ∧ p1) ∧ (p3 → p5))) ∧ p2)) ∧ (p4 ∨ ((True → (p5 ∨ (True → True))) → False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137743902079670645131932712624 : ((p2 ∨ (((p2 → (True ∧ ((p4 → ((p5 → p5) ∨ p3)) ∧ ((p1 ∨ (p3 → (p4 ∨ p3))) → p3)))) → p4) ∧ p1)) ∨ (p5 → (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711164889223856109935330325804 : ((((p2 ∧ ((p5 → (False ∧ True)) → p2)) ∧ (p1 ∧ ((((p2 ∧ (p2 → False)) → ((p1 ∨ (False ∧ p2)) ∨ False)) ∨ p1) ∧ (p1 → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49649351231530359158287013065 : (((((p5 → p3) ∨ (p1 ∨ p5)) → (p4 ∨ (p2 ∧ ((p2 ∨ (False ∨ ((p4 → (False → p1)) ∨ p1))) ∧ p5)))) → ((p3 ∧ True) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192724491455721522751310575970 : ((((True ∨ (False → p1)) → ((p3 → p3) ∨ p4)) → p5) → ((((True → (p1 ∨ True)) ∨ (False → p5)) ∨ ((False ∨ (True ∧ True)) → p3)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662073466713100519964713139656 : (((((p3 ∨ (False ∧ ((False ∧ ((False ∧ (p3 ∨ False)) → True)) ∧ p1))) ∧ ((((p4 ∧ p5) → (p1 → p4)) → False) → True)) → (p4 ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46159957875803813864061104915 : (((((p2 → (((p3 ∨ (p4 ∧ (((p3 ∧ False) ∧ p4) ∨ p1))) → True) ∨ p3)) ∧ ((p2 → p4) ∨ (p4 ∨ p1))) → p5) ∧ (False ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_145627567284385519832895063668 : (((p3 ∨ (p2 → True)) → ((p5 ∨ p3) ∨ (p2 → (((((p1 ∨ p5) ∧ p5) ∧ p1) ∧ p1) ∨ (p3 → p2))))) ∧ ((p5 ∨ p1) ∨ (p2 ∨ True))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324359598239945647642247604371 : (p5 ∨ (((p4 ∨ (p3 ∧ (p3 ∧ p3))) ∨ p1) ∨ (((((p4 ∨ p2) ∧ False) ∧ (p2 → (True ∧ p4))) → ((p1 ∧ False) ∨ True)) → (True ∨ p2)))) := by
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
theorem thm_5_vars_111834884312159370464537951794 : ((((((p3 → (True ∧ p4)) ∨ (((p5 ∨ (p3 → p4)) ∧ p4) ∨ (False ∨ (p3 ∧ p3)))) → p2) ∨ ((False ∧ p2) → p5)) ∨ p5) ∨ (False ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_345433405126552843503033378591 : (p3 → (((((p3 ∨ (((p4 ∨ True) ∨ p2) ∧ ((((p3 ∨ p1) ∨ False) ∨ (True → p1)) ∧ p2))) ∧ p1) → (p3 → p4)) ∧ (p3 ∧ p5)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115549552692582575937201348923 : ((((((p2 → p4) → p2) ∧ False) ∧ p3) ∧ (p1 ∨ ((p2 ∨ (p4 ∧ (p4 ∧ ((p5 ∧ (p1 → False)) → p3)))) ∧ (p5 → p2)))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113931267780365047720753793667 : (((((p1 → (p5 ∨ (True ∧ (p5 ∧ False)))) → (p3 ∧ p3)) ∨ ((False ∨ (p4 ∧ p1)) → (p5 ∨ p3))) ∧ (True → (False ∨ p1))) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328532331780726685325582783247 : (True → ((p4 ∧ ((((True ∧ (True → p1)) ∧ p4) ∧ ((p4 ∧ p5) ∨ False)) ∧ (p4 ∨ p2))) ∨ ((((p1 ∧ p3) ∧ p1) ∨ (p3 ∧ True)) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748265297024252410885995367897 : ((((p2 → False) → (((p2 ∨ ((((((p5 → (p5 ∨ (p5 ∨ p2))) ∧ p2) ∨ False) → p5) → (False ∧ p3)) → (True ∧ False))) → p2) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191010953288468262723405346854 : (((p1 ∨ (p3 ∧ (p3 ∨ p4))) ∨ (True → (p4 → p1))) ∨ (p5 → (((p3 → (p3 → False)) ∧ p5) ∨ (((p5 → p2) ∨ (p4 ∧ p2)) ∨ p5)))) := by
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



