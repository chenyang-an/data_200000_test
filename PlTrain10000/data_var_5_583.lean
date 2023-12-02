variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190154349939824233906676314231 : ((((True → p2) → (p5 ∧ ((p4 ∧ False) ∨ p3))) ∧ False) ∨ (((p4 → p4) → p3) → (((((p5 ∨ (p5 ∨ p4)) ∨ p4) ∨ p1) → p1) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44821359718429512305068162703 : ((((True → (True → False)) ∧ (((p2 ∨ (False ∧ ((True ∨ ((p4 → p3) ∨ p5)) ∧ False))) → (p2 → ((p5 → p2) → p3))) ∨ False)) → p1) ∨ p3) := by
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h8 := h6 h7
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785960677340670685918452426115 : (((p4 ∨ ((((p2 → ((p5 → (p2 ∧ (((p2 → True) → p4) → p1))) ∧ (p5 → (p2 ∨ p1)))) → p2) ∨ (p1 → p2)) ∨ (p3 ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38450854130885508418235512530 : ((((((((p1 → False) ∧ (True ∨ False)) → ((False → p3) ∧ p5)) ∧ p5) ∨ p4) → (p3 ∨ ((True → (False ∨ (p2 → p2))) ∧ p5))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112407856112719617777981543451 : ((((p2 ∧ ((False → ((p3 ∨ ((p2 ∨ ((p4 → False) ∧ (p2 ∨ p3))) → (True → False))) ∨ p4)) ∨ (p5 → p4))) ∧ True) → False) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670582336168211861335251383878 : (((((p5 ∨ p5) ∨ ((((((p4 ∧ (((p5 ∨ p5) ∧ p2) ∨ p1)) → p3) ∨ (True ∨ p3)) → p4) ∧ p2) ∨ p3)) ∨ ((False ∧ p4) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48815169873203453695848246535 : (((p3 ∧ (False ∨ (p4 ∧ ((p4 ∨ (p4 → (p1 → p4))) ∨ (p3 ∧ ((p1 ∨ (p2 ∨ p5)) → (p4 ∨ p2))))))) ∧ (False ∨ (p5 → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215777197833720789213169608649 : ((p1 ∨ ((p2 → p4) → p2)) ∨ (p2 ∨ (p1 → (p1 ∨ (((p4 ∨ ((True ∨ (p5 ∨ (p3 ∨ p4))) → ((p5 → p1) ∨ p1))) → p4) → p3))))) := by
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
theorem thm_5_vars_55058535316936534040441736337 : (((p2 ∨ ((p5 ∧ (False ∧ p1)) ∧ True)) ∧ ((True → p3) ∧ (((p4 → (p5 → (p5 ∧ ((p2 ∧ p3) ∨ False)))) ∨ p2) ∨ (False ∨ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46400543572193311868946027806 : (((((p5 ∨ p5) → (((p5 ∨ p4) ∧ p4) → False)) ∧ (p1 → (True ∧ ((p3 ∧ ((False ∧ p2) ∨ (p4 ∧ False))) → False)))) ∧ (p2 ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_784978761968856900527544888041 : (((p3 ∨ (p4 → ((p5 ∧ (p3 → p3)) → (p2 → ((p5 → (p5 → (p4 → ((True → (p3 → False)) ∧ p3)))) ∨ ((True ∨ p4) ∨ p3)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159818225699064761411907211776 : (((False ∨ (p4 ∨ ((False ∧ p4) → ((p4 → False) → (((False → (False ∧ p2)) ∨ p1) → p1))))) ∨ p2) → ((p5 → p3) ∨ (False ∨ (False ∨ True)))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357903253703695044601431527386 : (p5 → (p5 ∧ (p3 → ((((p4 ∧ p4) ∧ False) ∧ (p4 ∨ (p4 ∧ (p3 → ((p2 → (((p5 → False) ∧ p3) → True)) ∧ True))))) ∨ (p4 ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63235003311928999766800464138 : ((p5 ∧ ((((False ∧ False) → ((p5 ∨ (False ∧ p5)) ∧ (p4 ∨ p2))) → p5) ∧ (((True ∨ True) → (((p3 ∧ True) ∧ p3) ∨ p3)) ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55336639473291369537809610201 : (((p5 ∨ (p1 ∨ (p5 ∨ (True ∧ p4)))) ∨ (p5 ∨ ((True → False) ∧ (False → (((p1 → p1) ∨ True) ∨ (p5 ∨ (p2 → (False → p1)))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60530207554751920452588195662 : ((True ∧ (((p2 → ((p4 ∨ p1) ∨ (((p4 → ((p2 → p4) → p1)) ∧ ((((p5 ∧ True) → p4) ∧ True) → p4)) → p1))) → p3) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192791487368085514379701195783 : (((p2 ∨ ((True → (True ∧ True)) ∨ (p3 ∧ True))) → p5) → ((False ∧ ((p2 ∧ (((p5 ∨ p5) ∧ p4) → (True ∧ False))) ∨ p1)) ∨ (False → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615311137426218269844293718813 : ((((((((True → ((True ∨ False) ∨ p4)) ∧ p2) → ((False ∧ (p5 → p4)) ∧ p2)) → p1) ∨ (p5 → (False ∨ (False → (False ∧ False))))) ∨ p5) ∨ p2) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_625820950658837625462720198396 : ((((p1 → (True → (p5 ∨ ((p2 ∨ ((p5 ∧ (p2 ∧ True)) ∧ ((p4 ∨ p2) ∧ (p3 ∧ p3)))) ∧ ((p1 ∨ p3) ∨ (p2 → p4)))))) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309719977400303462895799188740 : (p2 ∨ ((p1 ∨ ((p3 ∧ p2) ∨ ((((((p2 ∨ (p5 ∨ p5)) ∨ False) → False) ∨ p3) ∨ p4) → (p1 ∧ (p3 ∨ False))))) → (p2 ∨ (p5 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349978410089785837115644790588 : (p4 → (((((((((p5 ∧ ((p2 ∧ True) ∨ p1)) ∨ p4) ∧ p3) ∧ ((p5 ∧ (p5 ∨ p5)) ∨ (p3 → p5))) ∨ p2) → p2) ∨ p3) ∨ p4) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152974111373664071969011162820 : ((p1 ∧ ((((p5 ∨ p4) ∧ ((p3 → (p3 ∨ p3)) ∨ p4)) ∧ ((p5 ∨ p5) ∧ p1)) ∧ ((True → p5) ∨ p5))) → (p4 ∨ (p4 ∨ (p2 → p1)))) := by
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
  let h8 := h6.left
  let h9 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h7.left
      let h13 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h16
          -- One of the premise coincides with the conclusion.
          exact h13
        case inr h17 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h18
          -- One of the premise coincides with the conclusion.
          exact h13
      case inr h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h21
          -- One of the premise coincides with the conclusion.
          exact h13
        case inr h22 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h23
          -- One of the premise coincides with the conclusion.
          exact h13
    case inr h24 =>
      -- Conjunctions on the left can always be decomposed.
      let h25 := h7.left
      let h26 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h25
      case inl h27 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h28 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h24
        case inr h29 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h24
      case inr h30 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h31 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h24
        case inr h32 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h24
  case inr h33 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h34 =>
      -- Conjunctions on the left can always be decomposed.
      let h35 := h7.left
      let h36 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h35
      case inl h37 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h38 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h33
        case inr h39 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h33
      case inr h40 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h41 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h33
        case inr h42 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h33
    case inr h43 =>
      -- Conjunctions on the left can always be decomposed.
      let h44 := h7.left
      let h45 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h44
      case inl h46 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h47 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h43
        case inr h48 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h43
      case inr h49 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h50 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h43
        case inr h51 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h43



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319391714889517795510258044008 : (p4 ∨ (((p3 → ((((p2 ∧ p2) → (p3 ∨ p5)) ∨ (p1 ∨ p3)) → p3)) ∨ p5) → (((p1 ∨ (p5 → ((False ∨ p1) ∨ p5))) ∨ p5) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_797374526402649214760553029959 : (((p1 → (((p2 ∨ ((p3 ∨ p1) → p2)) → (p1 ∧ ((((((p2 ∨ True) ∨ p3) ∨ p1) ∧ p2) ∧ ((p1 ∧ p5) ∨ False)) ∨ p1))) ∨ p5)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_623918450492117727733284874159 : ((((p2 ∨ (((((False → (p2 ∨ False)) ∨ p3) → ((p4 ∨ ((((False ∨ p2) → p2) → (p4 ∨ p3)) ∧ p3)) ∨ p5)) ∨ True) ∧ p3)) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_106311035890632572780247167874 : (((((p4 ∨ ((p2 ∨ p2) ∧ p5)) ∧ (p4 ∨ p5)) → p4) ∨ (p3 → (((True → (p2 → True)) → (True ∧ p4)) → (p4 ∧ p4)))) ∧ (False → p4)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (True → (p2 → True)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h3
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h8 : (True → (p2 → True)) := by
    -- Implications on the right can always be decomposed.
    intro h9
    -- Implications on the right can always be decomposed.
    intro h10
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h11 := h2 h8
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- One of the premise coincides with the conclusion.
  exact h12
  -- Implications on the right can always be decomposed.
  intro h13
  -- False on the left can always be used.
  apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_588303210964007115781248256590 : ((((((((p2 ∧ True) → False) ∨ p5) ∧ (((p5 ∨ ((True ∨ p5) ∧ p2)) → ((False ∨ ((p3 ∨ p3) → p2)) → p4)) → p3)) ∨ p5) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57097112694830580232363515992 : ((((p5 ∧ False) ∧ False) ∨ (p5 ∨ ((p5 ∨ (((p4 ∧ p2) ∨ ((p4 → False) ∧ p1)) ∧ ((p5 ∨ (p2 → p1)) ∧ p5))) ∨ (p2 → p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_730341908645447681241778014434 : (((((p5 → p5) → False) → ((False ∨ p4) ∨ (p1 ∧ (((p5 ∧ ((((p1 ∨ p2) ∧ p3) → True) ∧ p4)) ∨ p3) → ((p4 ∧ p2) ∧ True))))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 → p5) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141903532820526365556243386468 : (((p5 → True) ∨ (((p4 ∨ ((p1 ∨ p5) ∨ ((p3 ∨ (True → (p1 ∨ p3))) ∨ p1))) ∨ (p3 ∧ (True → p5))) ∨ False)) → (p2 ∨ (True ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
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
          -- Disjunctions on the left can always be decomposed.
          cases h7
          case inl h8 =>
            -- Disjunctions on the left can always be decomposed.
            cases h8
            case inl h9 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h10 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- True on the right can always be proven directly.
              apply True.intro
          case inr h11 =>
            -- Disjunctions on the left can always be decomposed.
            cases h11
            case inl h12 =>
              -- Disjunctions on the left can always be decomposed.
              cases h12
              case inl h13 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- Show the left disjunct based on <expert-advice>.
                apply Or.inl
                -- True on the right can always be proven directly.
                apply True.intro
              case inr h14 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- Show the left disjunct based on <expert-advice>.
                apply Or.inl
                -- True on the right can always be proven directly.
                apply True.intro
            case inr h15 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- True on the right can always be proven directly.
              apply True.intro
      case inr h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h16.left
        let h18 := h16.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h19 =>
      -- False on the left can always be used.
      apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159290053184655648604854483259 : ((p4 → ((p5 ∨ True) → (((((True ∨ (p3 ∨ p1)) ∨ (p3 ∧ True)) ∨ p3) ∧ (p1 → p2)) → False))) ∨ (p4 ∨ (False → (p1 → (p4 ∧ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148177353317235265699648546581 : ((((p1 ∨ ((True ∧ ((p5 ∧ p3) ∧ ((p1 → False) ∨ p1))) → (p4 ∧ p2))) → p5) ∧ ((p2 ∧ True) ∧ p2)) ∨ ((p1 → (p4 ∧ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198533576568330119838066876083 : ((False ∨ ((p5 ∨ p1) ∧ (p5 ∧ (p5 ∨ p5)))) ∨ (p5 ∨ (((p1 ∨ (p5 → ((True ∧ p1) → (False ∨ (p3 ∨ p3))))) ∧ False) ∨ (p2 ∨ True)))) := by
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
theorem thm_5_vars_87387004111374304807690661988 : (((p1 ∧ (p4 ∧ ((True → False) ∨ False))) ∧ (((p1 → (((p4 → False) ∨ ((p2 ∧ p2) ∨ False)) → (p2 ∨ (p1 → p4)))) ∨ p3) ∨ True)) → False) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h11 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h12 := h8 h11
        -- False on the left can always be used.
        apply False.elim h12
      case inr h13 =>
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h14 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h15 := h8 h14
        -- False on the left can always be used.
        apply False.elim h15
    case inr h16 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h17 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h18 := h8 h17
      -- False on the left can always be used.
      apply False.elim h18
  case inr h19 =>
    -- False on the left can always be used.
    apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747216525849051319675699982190 : ((((p5 ∨ p1) → (((((p4 ∨ (False ∧ True)) ∨ (p5 ∨ False)) ∨ (True ∨ False)) → False) ∨ (((p5 → ((p2 → p5) → True)) ∧ p2) ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322773587543666964809871634786 : (p5 ∨ (((((p4 → False) ∧ ((p5 ∧ ((p3 ∨ (False ∨ p2)) → p5)) ∧ (p4 ∨ (p1 ∧ (p5 ∨ p4))))) ∨ p1) ∧ (p1 → (p2 ∨ p5))) → p1)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h11 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h12 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h11
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h13 := h5 h12
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
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
  case inr h19 =>
    -- One of the premise coincides with the conclusion.
    exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147892798099702905972563488356 : (((((((p5 ∨ ((p5 ∨ p5) ∨ (p5 ∧ (p3 → (p5 ∧ p2))))) ∨ p3) ∧ p2) → p1) ∨ p1) ∧ (p1 ∨ p3)) ∨ ((p5 ∨ p4) ∨ (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_98810147597489693894696463004 : ((True → ((((p2 ∨ (((p2 → p3) ∧ (p4 → (p3 ∧ p2))) ∧ p2)) ∧ (p3 ∨ True)) ∧ (p2 ∧ (p2 ∧ (p3 ∧ (p3 ∨ p3))))) ∧ False)) → p1) := by
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113027029434814723648500530170 : (((True ∨ ((True ∨ ((True ∧ p5) → (p2 ∧ (p2 ∨ p4)))) ∨ ((p5 → p1) → (((p2 ∨ p4) ∧ (p2 ∨ p5)) ∨ p3)))) → p3) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136091100321205164600766678048 : ((((p1 ∧ (False → ((True → p2) ∧ p5))) ∧ p1) ∨ ((p2 → p4) ∧ ((p3 ∧ ((p3 ∧ p1) ∧ True)) ∨ (p1 → p3)))) ∨ ((p3 → p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_7997228596657719871433926532 : ((((((((p3 ∧ p2) → ((False → (False → (False ∨ p3))) ∨ p4)) → (p1 → (p3 → p1))) ∨ ((p1 ∧ False) ∨ True)) → False) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_62550096489395446513312747156 : ((p3 ∧ (p3 ∨ (((p2 ∧ ((p1 ∨ True) → ((False ∧ True) → p1))) → ((p4 ∧ (p1 → True)) ∧ ((p5 ∨ p3) ∧ (p2 ∨ p1)))) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351655937428798619909736781202 : (p4 → ((((True → ((True ∨ (((p5 ∨ True) → p3) ∨ True)) ∧ p5)) → (False → p2)) ∧ p1) → ((((p4 ∨ p5) ∧ (p2 → p4)) → p3) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340763214934209874337082397505 : (p2 → (((p5 ∨ (((((False ∨ p1) ∧ ((p3 ∧ (False ∧ p4)) ∨ True)) ∨ (True ∨ (False ∨ (False ∧ p1)))) ∨ False) ∧ (p1 → True))) ∨ False) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197285883838782206436669237374 : ((((p3 → (False → p2)) ∨ (False ∨ p2)) → p2) ∨ (p4 → ((p2 ∧ (p5 → ((p3 ∧ True) ∧ False))) ∨ ((False ∨ True) ∧ ((p5 ∨ p3) → p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_710107633240722962783430769891 : (((((((p5 ∨ False) ∨ False) ∧ p1) ∨ p5) ∧ (((((False ∧ False) ∨ (((True ∧ p4) ∨ p5) ∨ (p4 ∧ (p3 ∧ p3)))) ∨ p2) ∨ True) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227842565489139894915263266891 : ((p2 ∧ (p5 ∧ p4)) ∨ ((((p3 ∧ ((True ∨ (p4 → (p3 → p2))) ∧ (p3 → (p1 → (p1 ∨ p2))))) ∧ p2) ∧ ((p2 ∨ p2) ∧ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258785592808121565042813352203 : ((True → False) → ((True ∨ ((((p4 ∧ (False ∧ (False ∨ p1))) ∧ p1) ∨ (p4 ∨ False)) ∨ p3)) → (p4 ∧ ((((True → True) ∨ p2) ∧ p2) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h5 := h1 h4
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Conjunctions on the left can always be decomposed.
        let h11 := h9.left
        let h12 := h9.right
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- False on the left can always be used.
        apply False.elim h13
      case inr h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h16 =>
          -- One of the premise coincides with the conclusion.
          exact h16
        case inr h17 =>
          -- False on the left can always be used.
          apply False.elim h17
    case inr h18 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h19 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h20 := h1 h19
      -- False on the left can always be used.
      apply False.elim h20
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h21 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h22 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h23 := h1 h22
    -- False on the left can always be used.
    apply False.elim h23
  case inr h24 =>
    -- Disjunctions on the left can always be decomposed.
    cases h24
    case inl h25 =>
      -- Disjunctions on the left can always be decomposed.
      cases h25
      case inl h26 =>
        -- Conjunctions on the left can always be decomposed.
        let h27 := h26.left
        let h28 := h26.right
        -- Conjunctions on the left can always be decomposed.
        let h29 := h27.left
        let h30 := h27.right
        -- Conjunctions on the left can always be decomposed.
        let h31 := h30.left
        let h32 := h30.right
        -- False on the left can always be used.
        apply False.elim h31
      case inr h33 =>
        -- Disjunctions on the left can always be decomposed.
        cases h33
        case inl h34 =>
          -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
          have h35 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h1, we can now drive its conclusion.
          let h36 := h1 h35
          -- False on the left can always be used.
          apply False.elim h36
        case inr h37 =>
          -- False on the left can always be used.
          apply False.elim h37
    case inr h38 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h39 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h40 := h1 h39
      -- False on the left can always be used.
      apply False.elim h40



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_803430163391566123800396515688 : (((p3 → ((p3 → (p2 ∨ ((((True ∧ p2) ∨ p2) ∧ ((p1 ∧ p5) ∧ ((((p5 ∨ False) → p4) → (p2 ∨ p2)) ∧ p2))) ∧ p4))) ∨ p3)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136109908636827522061317852595 : ((((p3 → (p2 → True)) → (p2 → (p4 ∧ False))) ∨ ((p1 → (p3 → (False ∨ (True ∧ (p2 ∧ False))))) → (p4 ∧ True))) ∨ (p3 → (True → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249546156378966505105649839928 : ((p5 ∨ p2) ∨ (((((True → ((((p2 ∨ (p3 ∨ p2)) → (False → p3)) ∨ True) ∧ False)) ∧ (p3 → p2)) ∧ p2) ∧ (p4 → p4)) → (p5 → p4))) := by
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
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h9 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h10 := h7 h9
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774848813618582436040622132048 : (((False ∨ ((p4 ∨ ((p2 ∧ p3) ∨ p4)) ∧ (p1 → ((True ∧ (p2 ∧ ((p3 → (p5 ∧ (p2 → p2))) → (p3 ∧ (p5 ∧ p4))))) ∨ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64597087498907902019735287053 : ((p1 ∨ ((p3 ∨ p4) ∨ (((((((((p1 → p2) ∨ False) → True) → p3) ∨ True) → p3) → ((False ∨ (p3 ∧ p2)) ∧ p2)) ∨ p3) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158508427302553024482152896303 : (((False ∨ p2) → (((((p1 ∨ p5) ∨ (True → p5)) ∨ p4) ∨ (((p3 ∨ True) ∨ p5) ∧ p1)) ∧ p4)) ∨ ((p2 ∧ p5) ∨ ((p5 ∧ False) → p4))) := by
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
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356740061321737717347663113418 : (p5 → ((p4 ∧ (((True ∧ p5) → False) ∨ p1)) ∨ (p1 ∨ ((((p3 ∧ (p2 ∨ (p2 ∧ p1))) ∨ p5) ∨ p2) ∨ ((False ∧ p1) ∧ (False ∨ p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256907693410799913830816783985 : ((p1 ∨ p4) → (((p2 → (p2 ∧ (p5 → p5))) → p1) ∨ ((((p3 → (p5 ∨ ((p5 ∧ (p2 ∨ p2)) → (p2 → p4)))) ∧ p3) ∧ False) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251146025024402804143444010074 : ((p2 → False) ∨ ((False ∨ p3) ∨ ((True ∧ True) → (p3 ∨ (p1 ∨ (p3 ∨ (True ∧ (((True ∧ True) ∧ p2) ∨ (False → ((True ∧ p5) ∧ p2)))))))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115933667444977019295667156952 : (((p3 ∧ ((p3 → True) → p3)) ∨ (((p4 ∨ (True ∨ ((p5 ∧ ((p2 → p1) ∨ (p5 ∨ False))) → p1))) ∨ (p1 ∧ p3)) ∧ p1)) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51206714661815330048231113482 : (((((p2 ∨ (((p1 → p3) ∨ False) → p5)) ∨ p3) ∧ (((p3 ∨ p3) ∧ p3) ∨ (p5 → p3))) ∨ (p2 ∨ (((p1 ∨ False) ∧ p5) → p5))) ∨ False) := by
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
  cases h2
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50268612677972608190275672479 : ((((True ∧ (p2 ∧ ((p4 ∧ p4) ∧ (((p2 ∧ (p2 → p4)) → (p4 ∧ p2)) ∧ True)))) ∧ (True ∧ p3)) ∨ ((p3 → (False → p2)) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_589407577950066807853597717545 : (((((((p4 → ((((p2 ∨ False) ∨ p1) → (True → False)) ∨ (True → p3))) → (p3 → ((p3 ∧ (p2 ∨ False)) → p3))) ∨ True) → p2) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347105335155221990417495732699 : (p3 → (((((p2 ∧ (False → p2)) ∨ (p5 ∧ p4)) → (True ∨ p1)) → (p2 ∧ p5)) ∨ ((p2 → (((p2 ∧ p2) → (p1 → p3)) ∧ p4)) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119139274837799022009224825279 : ((p1 → (p5 ∨ ((True ∨ p2) → ((p2 ∧ (True ∧ (p4 ∨ (False ∨ p1)))) ∧ (((p1 ∨ False) ∨ (p5 → p4)) ∧ (p5 ∧ p1)))))) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731748696767273151234921427306 : ((((p3 → (p3 ∧ False)) → ((p3 ∧ (False ∨ (((((p3 ∧ (p4 ∨ p3)) → ((p1 ∨ p2) ∨ p4)) ∨ (True ∨ p4)) → False) → p2))) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249974345435099297175371426524 : ((True → p2) ∨ ((((((True → ((p5 ∧ False) ∧ (True → True))) ∨ True) ∨ (False → ((p3 → False) → False))) ∧ True) → p4) → ((p1 → p2) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((((True → ((p5 ∧ False) ∧ (True → True))) ∨ True) ∨ (False → ((p3 → False) → False))) ∧ True) := by
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305594869691650832700450859442 : (p1 ∨ (((p4 ∨ p3) ∨ (True ∧ (((p3 ∨ (p1 ∧ p3)) ∨ False) ∧ p5))) ∨ (p2 ∨ ((False ∨ p2) → ((p3 ∨ (p3 ∧ p4)) ∨ (False → p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136862640821495007617383212014 : (((p5 ∧ p5) ∨ (p3 ∧ ((((p1 ∨ p5) → True) ∧ p3) ∨ (False ∧ (False ∧ (p5 ∧ ((p1 ∧ p2) ∧ (p2 → p5)))))))) ∨ (True ∨ (False → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678144634205990271076490370980 : ((((((False ∧ False) ∨ (p1 ∧ (p2 ∧ (p3 → ((p4 ∨ p5) ∧ False))))) ∨ ((p5 ∨ p2) → (False ∨ True))) ∨ (p5 → ((False → False) ∨ p5))) ∨ p5) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50911250311980885143222729523 : ((((True ∧ (p1 ∨ ((p1 → ((p3 ∨ ((p4 → p1) → True)) ∨ False)) → p5))) ∨ (p4 → p1)) ∧ (True ∧ (p1 → (p5 → (p2 ∧ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343380303668985607067447714485 : (p2 → ((True ∧ p5) ∨ ((False ∨ (p4 → p1)) ∨ ((((p3 → p2) ∨ (p2 → True)) ∨ p4) → ((((p5 → False) ∨ p4) ∧ p4) ∨ (True ∧ True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
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
theorem thm_5_vars_201096244683900720042333621856 : ((True → ((p1 ∨ (p5 ∨ (p5 → p4))) ∧ p1)) → (p2 ∨ ((((False ∨ p2) ∧ p2) ∧ p3) → ((((p1 ∧ p4) ∨ p1) ∧ p2) ∧ (p3 ∨ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h10 := h1 h9
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11
  -- Conjunctions on the left can always be decomposed.
  let h12 := h2.left
  let h13 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h12.left
  let h15 := h12.right
  -- Disjunctions on the left can always be decomposed.
  cases h14
  case inl h16 =>
    -- False on the left can always be used.
    apply False.elim h16
  case inr h17 =>
    -- One of the premise coincides with the conclusion.
    exact h15
  -- Conjunctions on the left can always be decomposed.
  let h18 := h2.left
  let h19 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h20 := h18.left
  let h21 := h18.right
  -- Disjunctions on the left can always be decomposed.
  cases h20
  case inl h22 =>
    -- False on the left can always be used.
    apply False.elim h22
  case inr h23 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344357028235771211328531101425 : (p2 → (p4 ∨ ((((p3 ∧ p5) ∨ ((False → ((False ∨ ((p2 ∨ (((p1 ∨ False) ∧ True) → p3)) ∧ p3)) → True)) → p4)) ∨ True) ∧ (p2 ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232729541648105257028681151709 : ((p1 ∧ (True → p4)) → (True ∧ (True → ((False ∧ (p3 ∨ (((p1 ∨ (p4 ∧ p5)) → (p2 ∧ ((p3 ∧ (p1 ∨ p3)) ∨ False))) ∨ p3))) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305627476719179387989390861129 : (p1 ∨ ((p3 ∧ (p1 ∧ ((((p5 ∧ (p2 ∨ True)) ∧ p3) ∨ True) ∧ p5))) → (p1 ∧ (((p4 ∨ True) ∨ (True ∧ p1)) → ((p5 → p4) ∨ p1))))) := by
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
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h14 =>
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h15 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  -- Implications on the right can always be decomposed.
  intro h16
  -- Disjunctions on the left can always be decomposed.
  cases h16
  case inl h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h1.left
      let h20 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- Conjunctions on the left can always be decomposed.
      let h23 := h22.left
      let h24 := h22.right
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h25 =>
        -- Conjunctions on the left can always be decomposed.
        let h26 := h25.left
        let h27 := h25.right
        -- Conjunctions on the left can always be decomposed.
        let h28 := h26.left
        let h29 := h26.right
        -- Disjunctions on the left can always be decomposed.
        cases h29
        case inl h30 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h21
        case inr h31 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h21
      case inr h32 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h21
    case inr h33 =>
      -- Conjunctions on the left can always be decomposed.
      let h34 := h1.left
      let h35 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h36 := h35.left
      let h37 := h35.right
      -- Conjunctions on the left can always be decomposed.
      let h38 := h37.left
      let h39 := h37.right
      -- Disjunctions on the left can always be decomposed.
      cases h38
      case inl h40 =>
        -- Conjunctions on the left can always be decomposed.
        let h41 := h40.left
        let h42 := h40.right
        -- Conjunctions on the left can always be decomposed.
        let h43 := h41.left
        let h44 := h41.right
        -- Disjunctions on the left can always be decomposed.
        cases h44
        case inl h45 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h36
        case inr h46 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h36
      case inr h47 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h36
  case inr h48 =>
    -- Conjunctions on the left can always be decomposed.
    let h49 := h48.left
    let h50 := h48.right
    -- Conjunctions on the left can always be decomposed.
    let h51 := h1.left
    let h52 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h53 := h52.left
    let h54 := h52.right
    -- Conjunctions on the left can always be decomposed.
    let h55 := h54.left
    let h56 := h54.right
    -- Disjunctions on the left can always be decomposed.
    cases h55
    case inl h57 =>
      -- Conjunctions on the left can always be decomposed.
      let h58 := h57.left
      let h59 := h57.right
      -- Conjunctions on the left can always be decomposed.
      let h60 := h58.left
      let h61 := h58.right
      -- Disjunctions on the left can always be decomposed.
      cases h61
      case inl h62 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h53
      case inr h63 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h53
    case inr h64 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h53



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299261051036520109504009509866 : (False ∨ ((((p5 ∧ ((((((p1 ∨ p4) → p5) ∧ p1) → (False → True)) ∨ False) ∧ (p3 → p1))) → False) → ((p1 ∨ (p4 ∧ p2)) ∧ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249068724460093661896087670921 : ((p4 ∨ p1) ∨ ((((True ∨ False) ∨ (True → p1)) → ((p4 ∧ False) ∧ (False ∧ (p3 ∨ p1)))) → (((p3 ∨ p5) → (True ∧ (p5 ∨ True))) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((True ∨ False) ∨ (True → p1)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233536783009611800377766270169 : ((p1 ∨ (p3 ∨ p1)) → ((p4 ∧ (p2 ∧ p1)) → (((p1 ∧ (((((p4 → p5) → False) ∧ p3) ∨ p3) ∨ True)) ∧ (p4 ∨ True)) ∨ (p2 → p5)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h10
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316712907133053856270955309499 : (p3 ∨ (p5 ∨ (False ∨ ((p2 ∧ ((p1 ∧ (True → p3)) ∨ (False → (p4 ∧ (((p2 ∧ (p3 ∧ False)) → True) ∧ (False ∧ p2)))))) ∨ (False → p4))))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171535499646785278259063646317 : ((((((False ∧ True) → True) → ((p5 ∧ p3) ∧ ((p3 → False) ∧ False))) ∨ False) ∨ True) ∨ (((((p3 → p4) ∧ (False → False)) ∨ p5) ∨ p4) → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171443312893624906051688952547 : (((False ∧ ((p3 ∨ (p1 ∧ ((p3 → (p1 ∧ p4)) → False))) ∧ (p1 ∧ p2))) ∧ True) ∨ ((False → (p2 → (p2 ∨ (p3 ∧ p1)))) ∨ (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695587727545923188504277068347 : (((((p2 ∨ (p1 ∨ ((p3 ∨ False) → (p4 ∧ p4)))) → ((p1 ∧ False) → p4)) → ((p5 → (p4 ∨ True)) → ((p1 → (p4 → True)) ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2303300836105596120719698103 : ((((p4 → (p1 → (((p2 ∧ p1) ∧ p4) ∧ p1))) ∨ (p5 → False)) ∨ False) → (p4 ∨ (p1 ∨ ((p5 ∨ (True ∨ (False ∧ p3))) ∨ p1)))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
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
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251659529699464386977470811600 : ((p3 → p2) ∨ ((((p2 ∧ (p4 → ((p4 → p3) ∧ True))) → ((False ∨ p5) ∧ True)) ∨ (((p5 → p3) → (p2 ∧ False)) ∨ (p4 → True))) ∨ p5)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_605467157919899306158545736101 : ((((p3 → ((p4 ∧ p3) ∧ (((p4 ∧ p4) ∧ p2) → (((True ∧ p1) ∨ p2) → (True ∧ (((p4 → p1) ∧ (True → p3)) ∨ p1)))))) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111901873555032956590883447963 : ((((((p2 ∧ p1) → (p3 ∨ ((p3 ∨ p5) ∧ p4))) → (p2 ∨ (True ∧ p2))) → (True → ((True → p3) ∨ (p2 ∨ True)))) ∨ p5) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_89355049504495887548283617860 : (((p5 ∨ (True → False)) ∧ (p1 ∨ (False → (((p2 ∨ p4) ∧ p1) ∨ ((p5 ∨ False) ∧ (p3 ∧ (p1 → (((p2 ∧ p5) → False) ∧ p4)))))))) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h6 =>
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h8 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h9 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h10 := h7 h9
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h12 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h13 := h7 h12
      -- False on the left can always be used.
      apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111191736502051841458271743894 : (((((True → p3) ∨ p2) ∧ ((p1 ∨ (True ∧ p5)) → ((True ∧ ((p2 → (((p5 → True) → p2) ∨ False)) ∧ p4)) ∨ p5))) ∧ False) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327121785085559213539866688688 : (True → (((p4 ∨ False) → ((p5 ∨ ((p3 ∨ (False ∧ ((False ∨ ((p1 ∧ (False ∧ True)) ∧ p4)) ∧ False))) ∧ ((p3 ∨ False) ∧ p3))) ∨ True)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62631189288751840378213609073 : ((p4 ∧ (((False ∨ p4) ∧ ((p5 ∧ p4) → (((True ∨ p5) ∧ ((True ∨ p2) → p1)) ∨ ((True → p2) ∨ ((p1 ∨ True) ∧ False))))) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310205676033426335640375601177 : (p2 ∨ ((((((((p4 → p1) → True) → p4) ∨ p3) ∨ True) → False) → False) ∨ (p2 ∨ (((((p1 ∧ False) → p5) ∨ (True → p3)) ∨ False) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729728875576289927824042983377 : (((((p3 → True) ∨ p1) → ((p4 ∨ (p3 ∧ True)) ∧ ((p2 ∨ ((p3 ∨ True) → p2)) ∨ ((((False ∧ (p3 ∧ p2)) ∨ p5) → p2) ∨ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40547360906875108489640948468 : ((((True → ((p3 → (True ∧ (p4 ∨ ((((p2 ∧ True) ∧ ((True → p2) ∧ True)) ∨ ((False ∨ p5) → p2)) ∧ p1)))) ∧ False)) ∨ True) ∨ p1) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357432110164948391437396530369 : (p5 → ((p4 ∨ p2) → ((((False ∨ (p3 ∧ (False ∨ p2))) ∧ ((False ∧ p1) → ((p3 ∨ (True ∨ ((p4 ∨ True) → False))) → False))) ∨ p5) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
    exact h1
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_120699310019839904369283766168 : ((((False ∨ ((p3 ∨ p1) → ((((p1 → False) ∧ (p5 → p4)) ∨ True) → (p5 → ((p1 → True) ∧ True))))) ∧ (p1 → p4)) ∨ True) → (p4 → p4)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_397148085225978185518441598450 : ((((p1 ∨ (((p5 ∧ (((p2 → False) → (p2 ∧ (p1 ∧ p1))) ∨ True)) ∨ (p2 ∨ ((((p4 → p2) ∧ False) ∧ p5) → p4))) ∨ p1)) ∨ False) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41927448808933691568038447905 : ((((p1 ∨ (p2 ∨ p3)) → (((((False ∧ p4) → p1) ∧ ((True → p4) → (p5 ∨ (True ∨ p1)))) ∧ (False ∨ (p2 ∨ p1))) ∧ p4)) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621087362115465670470933833 : (((((((p1 → False) → (p4 ∨ p4)) ∧ (p5 ∧ False)) ∨ p3) ∨ (((True ∧ (p1 → (p3 ∧ True))) → True) ∨ p1)) ∨ (p4 ∨ p5)) ∨ False) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50543862122040500366558816054 : (((((p5 ∧ ((False → p2) ∨ p4)) ∧ (((p2 ∨ False) ∨ True) → (True ∨ (p5 ∧ (True ∨ p5))))) ∨ p2) → ((True → False) ∧ (p2 ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51908784136894043555353500511 : ((((((p1 ∧ (p1 ∨ p5)) ∧ (p2 ∨ ((True → p3) ∨ p1))) ∧ p3) ∨ (False ∨ True)) ∨ (((True → (p4 ∧ (True ∨ p3))) ∧ False) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191799493111746743107139112028 : ((p2 ∨ (((p5 ∧ (p3 ∨ p3)) ∧ (p4 → p5)) → p2)) ∨ ((p2 → (p1 ∨ ((p4 → (((True → p2) ∧ (p1 ∨ True)) ∨ True)) → p2))) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



