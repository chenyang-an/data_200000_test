variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258467412620896412457468600273 : ((p5 ∨ p2) → (((True ∨ ((p2 → p1) → True)) ∧ ((p1 ∧ (p5 ∨ (p5 ∧ (p4 ∧ p1)))) ∧ (((p3 ∨ (p4 ∧ True)) ∧ False) → True))) → p1)) := by
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
    let h6 := h4.left
    let h7 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h11 =>
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h12 =>
        -- One of the premise coincides with the conclusion.
        exact h8
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h18 =>
        -- One of the premise coincides with the conclusion.
        exact h17
      case inr h19 =>
        -- One of the premise coincides with the conclusion.
        exact h17
  case inr h20 =>
    -- Conjunctions on the left can always be decomposed.
    let h21 := h4.left
    let h22 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h23 := h21.left
    let h24 := h21.right
    -- Disjunctions on the left can always be decomposed.
    cases h24
    case inl h25 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h26 =>
        -- One of the premise coincides with the conclusion.
        exact h23
      case inr h27 =>
        -- One of the premise coincides with the conclusion.
        exact h23
    case inr h28 =>
      -- Conjunctions on the left can always be decomposed.
      let h29 := h28.left
      let h30 := h28.right
      -- Conjunctions on the left can always be decomposed.
      let h31 := h30.left
      let h32 := h30.right
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h33 =>
        -- One of the premise coincides with the conclusion.
        exact h32
      case inr h34 =>
        -- One of the premise coincides with the conclusion.
        exact h32



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51985003343299424508297385784 : ((((p1 ∨ p3) ∨ (((False → p5) → (((True ∧ False) ∨ p4) ∨ p1)) ∨ (False ∨ True))) ∨ (p1 → (p1 → (((p4 → False) → p4) ∧ False)))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_60955151600887601594610819326 : ((False ∧ (((True → ((True ∨ (p3 ∧ ((p3 → ((p5 → (p1 → p1)) ∧ True)) ∧ (p2 → (p5 ∨ False))))) → (p1 ∨ p2))) → p1) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305036680409209685611245277074 : (p1 ∨ ((p1 → ((p1 ∨ (((((p1 ∧ (p2 ∧ p2)) → p3) → (p4 → p2)) ∨ (p1 ∨ (p5 → p5))) → p2)) → p3)) ∨ (True ∨ (True ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53283624107410766151234816539 : (((p4 ∧ (p5 ∨ ((p4 ∨ ((p4 ∧ p1) ∧ p2)) ∨ (p1 ∨ p1)))) ∨ (p3 ∨ ((False → ((True → False) ∨ False)) ∧ ((True ∧ p5) → True)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158076698807582648866198037591 : ((((False → (p4 ∨ p5)) ∨ (p2 ∧ True)) → ((False ∧ ((((p1 ∧ p4) ∧ False) → p2) ∨ p5)) ∧ p2)) ∨ (((p4 ∧ (p1 → p2)) → True) ∧ True)) := by
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
theorem thm_5_vars_688474323024408858949534324389 : ((((p5 ∧ ((((((p3 → (p5 ∨ True)) → False) → (p3 → p1)) → p2) → p1) ∧ p4)) ∧ ((True ∨ (((True ∨ p2) ∨ p4) ∨ p3)) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118202981857360605340546548822 : ((False ∨ (p4 → (((p5 → ((False ∧ ((p4 ∧ (p5 ∨ p3)) ∨ True)) ∧ ((p1 ∨ True) ∧ (p2 ∨ p1)))) ∧ (p1 → p2)) ∧ p5))) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_768191975002326969012669672257 : (((p5 ∧ (((True ∧ (((p4 ∧ True) → ((p3 → (p4 ∧ p5)) ∧ p5)) ∨ (False ∨ False))) ∨ (((p2 → p2) ∧ False) ∧ False)) → (False ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229141900640538405666979747243 : ((True → (p5 ∧ p4)) ∨ ((False ∧ (p2 ∧ True)) ∨ ((((True → ((p3 → p3) ∨ True)) ∧ p2) ∨ ((False ∨ (False ∧ p2)) ∧ p4)) ∨ (False → True)))) := by
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
theorem thm_5_vars_723704694096615412666074958998 : (((((True → p4) → p3) ∧ ((((((((p2 ∨ (p5 ∨ p1)) ∧ (p1 → True)) ∧ False) → p1) → p5) → p4) → (True → (p5 ∧ False))) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350319591658242382482487108646 : (p4 → ((p5 ∨ (p2 ∨ (((((False ∨ (p4 ∨ p4)) ∨ False) ∧ p1) ∨ (True → p1)) ∨ ((p5 ∨ ((p1 ∧ (p3 → p1)) ∨ p2)) → True)))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60229820691202841367725799295 : (((True → p3) → ((p5 ∨ (((True ∨ (True ∧ (p4 → p3))) ∨ p2) ∨ True)) → ((p3 ∨ p2) → (p1 ∨ (False → (p5 → (p1 → False))))))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    cases h2
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h6
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Disjunctions on the left can always be decomposed.
          cases h11
          case inl h12 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h13
            -- Implications on the right can always be decomposed.
            intro h14
            -- Implications on the right can always be decomposed.
            intro h15
            -- False on the left can always be used.
            apply False.elim h13
          case inr h16 =>
            -- Conjunctions on the left can always be decomposed.
            let h17 := h16.left
            let h18 := h16.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h19
            -- Implications on the right can always be decomposed.
            intro h20
            -- Implications on the right can always be decomposed.
            intro h21
            -- False on the left can always be used.
            apply False.elim h19
        case inr h22 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h23
          -- Implications on the right can always be decomposed.
          intro h24
          -- Implications on the right can always be decomposed.
          intro h25
          -- False on the left can always be used.
          apply False.elim h23
      case inr h26 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h27
        -- Implications on the right can always be decomposed.
        intro h28
        -- Implications on the right can always be decomposed.
        intro h29
        -- False on the left can always be used.
        apply False.elim h27
  case inr h30 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h31 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h32
      -- Implications on the right can always be decomposed.
      intro h33
      -- Implications on the right can always be decomposed.
      intro h34
      -- False on the left can always be used.
      apply False.elim h32
    case inr h35 =>
      -- Disjunctions on the left can always be decomposed.
      cases h35
      case inl h36 =>
        -- Disjunctions on the left can always be decomposed.
        cases h36
        case inl h37 =>
          -- Disjunctions on the left can always be decomposed.
          cases h37
          case inl h38 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h39
            -- Implications on the right can always be decomposed.
            intro h40
            -- Implications on the right can always be decomposed.
            intro h41
            -- False on the left can always be used.
            apply False.elim h39
          case inr h42 =>
            -- Conjunctions on the left can always be decomposed.
            let h43 := h42.left
            let h44 := h42.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h45
            -- Implications on the right can always be decomposed.
            intro h46
            -- Implications on the right can always be decomposed.
            intro h47
            -- False on the left can always be used.
            apply False.elim h45
        case inr h48 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h49
          -- Implications on the right can always be decomposed.
          intro h50
          -- Implications on the right can always be decomposed.
          intro h51
          -- False on the left can always be used.
          apply False.elim h49
      case inr h52 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h53
        -- Implications on the right can always be decomposed.
        intro h54
        -- Implications on the right can always be decomposed.
        intro h55
        -- False on the left can always be used.
        apply False.elim h53



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51241494178106227924296317157 : ((((False ∧ (False ∧ p2)) ∨ (((p1 ∨ p3) ∨ True) → ((p2 ∧ p3) ∨ ((True ∧ p5) → p4)))) ∨ ((p2 → p3) ∨ (False ∨ (False → p2)))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_265742452479631393113951990553 : (True ∧ (p3 ∨ (p5 ∨ (p2 → (p5 ∨ ((p5 ∧ (p4 ∧ p3)) ∨ (((True → p2) ∨ True) ∨ (((p2 ∧ (p5 ∧ (p4 ∧ True))) ∨ p4) ∨ p1)))))))) := by
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
theorem thm_5_vars_232010727032596613725618325695 : (((p2 ∨ p4) → p5) → (True → (((p2 ∧ ((p1 ∨ (False → True)) → (((p2 → p5) ∨ p5) → ((p3 ∧ True) → (p5 ∧ p4))))) ∧ False) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54015390403331808553470828011 : ((((p5 ∧ (((p4 ∨ p3) ∨ (p5 → p5)) ∨ True)) → p2) → (((p3 ∧ (True ∨ p5)) ∧ (p1 ∨ False)) → (p4 ∨ ((p2 ∧ p4) ∨ p1)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h9
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- False on the left can always be used.
      apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45109773125071185225576418411 : ((((p2 ∨ p5) → (p2 ∨ ((((((True ∧ (False → p4)) ∨ p5) → (p5 → p3)) ∧ p4) ∧ ((p1 → (False ∨ p3)) ∧ p2)) → p5))) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44387494028636518298745090255 : ((((((p5 ∧ (p1 → (p3 ∧ (p5 ∨ p2)))) → False) → (True ∨ (True ∧ p5))) ∨ (p3 ∧ (p5 ∧ (False ∨ (False ∨ (p3 → True)))))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232095690501257544928428821261 : (((p5 ∨ True) → True) → ((p5 ∧ p4) ∨ (((True → (p2 ∨ (p3 ∨ (p5 → (p2 ∨ ((((p3 ∧ p4) → p4) ∨ p1) ∨ p1)))))) ∨ p3) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_635672558394001404326298278744 : (((((p2 ∨ ((False → False) ∨ (((p3 ∧ (p4 → True)) ∨ (True ∧ p4)) → ((p5 → True) → True)))) ∨ (p1 ∧ (False ∧ (p1 → False)))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179242011270900528173403101810 : ((p5 ∧ ((p1 ∨ ((p1 ∨ (p5 ∧ (p5 ∧ (False ∧ p2)))) → p4)) → False)) ∨ (((p4 ∨ p2) ∧ ((p3 → p1) ∧ p2)) ∨ (False → (False ∧ True)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_266081837770301585930607302167 : (True ∧ (p2 → (((True → ((False ∧ ((True ∨ p4) ∨ p3)) ∧ p3)) ∧ (p1 → True)) → (((p3 ∨ (False ∨ ((p2 ∨ True) ∨ p3))) ∧ p2) → False)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h2.left
    let h8 := h2.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h10 := h7 h9
    -- We need to get the left conjuct of h10 based on <expert-advice>.
    let h11 := h10.left
    -- We need to get the left conjuct of h11 based on <expert-advice>.
    let h12 := h11.left
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h17 =>
          -- Conjunctions on the left can always be decomposed.
          let h18 := h2.left
          let h19 := h2.right
          -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
          have h20 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h18, we can now drive its conclusion.
          let h21 := h18 h20
          -- We need to get the left conjuct of h21 based on <expert-advice>.
          let h22 := h21.left
          -- We need to get the left conjuct of h22 based on <expert-advice>.
          let h23 := h22.left
          -- False on the left can always be used.
          apply False.elim h23
        case inr h24 =>
          -- Conjunctions on the left can always be decomposed.
          let h25 := h2.left
          let h26 := h2.right
          -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
          have h27 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h25, we can now drive its conclusion.
          let h28 := h25 h27
          -- We need to get the left conjuct of h28 based on <expert-advice>.
          let h29 := h28.left
          -- We need to get the left conjuct of h29 based on <expert-advice>.
          let h30 := h29.left
          -- False on the left can always be used.
          apply False.elim h30
      case inr h31 =>
        -- Conjunctions on the left can always be decomposed.
        let h32 := h2.left
        let h33 := h2.right
        -- We want to use the implication h32 based on <expert-advice>. So we show its premise.
        have h34 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h32, we can now drive its conclusion.
        let h35 := h32 h34
        -- We need to get the left conjuct of h35 based on <expert-advice>.
        let h36 := h35.left
        -- We need to get the left conjuct of h36 based on <expert-advice>.
        let h37 := h36.left
        -- False on the left can always be used.
        apply False.elim h37



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62971919438644954602279487380 : ((p4 ∧ (p2 ∨ ((((p1 ∧ p5) ∨ p5) → (p4 ∨ False)) → (((p5 ∨ p2) ∧ p4) ∧ ((p5 ∧ (True ∧ p2)) ∨ (p4 ∨ (True → True))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738989401489056383938814203683 : ((((p3 ∧ p2) ∨ ((True ∧ ((((p1 ∨ p4) ∧ p2) ∨ (True ∨ (True → (p1 ∨ p5)))) ∧ p2)) → ((p4 → p1) ∨ (p1 ∨ (p1 → p1))))) ∨ p4) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- One of the premise coincides with the conclusion.
      exact h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h16
      -- One of the premise coincides with the conclusion.
      exact h16
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_811659578389081921125185221355 : (((p5 → (p2 → ((p1 ∧ (False ∨ (p3 ∨ (((True ∨ p3) ∧ ((False ∨ p5) → ((False ∨ ((True → p4) ∨ p1)) ∨ p3))) ∨ p1)))) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45956700343413708412793163249 : (((p5 → ((p2 ∧ (p1 → (p4 → p4))) ∨ (((p4 → ((((p4 → (False ∧ (p3 ∨ p2))) → p2) ∨ True) ∨ p4)) → p2) → p4))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355946712630624150181871794816 : (p5 → ((p4 ∧ (((((False ∧ (False ∧ p1)) ∨ False) → (True → p2)) ∨ True) ∨ (p5 → (((p4 ∨ p5) ∧ True) ∨ p1)))) → ((p1 ∧ p1) ∨ p4))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137810969941081153009133288595 : ((p3 ∨ ((((((p1 ∧ (p2 → p3)) ∧ p3) ∨ ((p3 ∧ p3) → p2)) → p5) ∨ ((p3 ∧ False) ∨ (p2 ∨ True))) ∧ p2)) ∨ (True ∧ (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47163359278990816783998094907 : ((((((p1 ∧ (True ∨ (p5 → (False ∨ (p3 → p2))))) → p5) ∧ (p3 → p1)) ∧ (p3 ∨ ((p3 ∧ (p1 ∨ p1)) ∨ p1))) ∨ (False ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149488236644720034653090763091 : ((p1 ∧ ((p2 ∧ ((p5 → (p2 ∨ (((p2 → False) ∨ p2) → ((p3 ∧ (p4 ∨ p2)) → p4)))) ∨ p3)) ∧ p1)) ∨ ((p4 ∧ (False ∧ p2)) → p1)) := by
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
theorem thm_5_vars_680344195784524743406170423824 : (((((True ∨ ((True ∨ (((p1 → p3) ∨ p3) → (False ∨ (True ∧ p2)))) → p3)) ∨ (p1 → (True ∧ p5))) → (((p5 → p5) → p1) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53836452418490434963350796993 : ((((p2 ∧ (False → (True ∨ p3))) ∧ (p4 → (p1 ∨ p2))) ∨ ((p4 ∧ (p3 ∧ ((p4 → (p2 → ((p2 ∧ p5) ∨ p5))) → p4))) ∨ True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343412968456591542137343711000 : (p2 → ((p5 ∧ p4) ∨ (((False ∨ (((True → (((((p1 ∧ p3) ∨ p3) ∧ p2) ∨ p2) ∨ (p4 ∧ p5))) ∧ False) ∧ True)) ∨ p2) ∧ (p2 ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_936753655039596303660499126819 : ((((((p4 ∨ True) → (True ∧ p2)) ∨ p3) ∧ ((False ∨ (False → False)) → ((p1 → ((p1 → p3) ∧ (False → False))) ∧ (p1 ∧ (p5 ∧ False))))) → p1) ∧ True) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : (False ∨ (False → False)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h6
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h7 := h3 h5
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h12 : (False ∨ (False → False)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- False on the left can always be used.
      apply False.elim h13
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h14 := h3 h12
    -- We need to get the right conjuct of h14 based on <expert-advice>.
    let h15 := h14.right
    -- We need to get the right conjuct of h15 based on <expert-advice>.
    let h16 := h15.right
    -- We need to get the right conjuct of h16 based on <expert-advice>.
    let h17 := h16.right
    -- False on the left can always be used.
    apply False.elim h17
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_640931399878297836448876872563 : (((((True ∧ p4) ∨ (p3 → (((False → (False ∧ p1)) ∨ (((((p2 ∧ p3) → p4) → p1) → True) ∨ (True ∨ (False ∧ True)))) ∧ False))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777060245929182287485933658145 : (((p1 ∨ (((False ∧ True) ∨ (p2 ∧ ((((((True ∧ p2) ∨ p1) ∨ False) ∧ False) → (p4 ∨ (False ∧ (p2 → False)))) → p1))) ∨ (False → p2))) ∨ p1) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774817267778077302749883656429 : (((False ∨ ((True ∨ (p1 → ((True ∨ p4) ∧ True))) → ((((p1 ∨ ((False ∨ p3) ∨ ((p4 ∨ p1) ∧ p1))) → p3) ∧ False) ∨ (False → p2)))) ∨ False) ∧ True) := by
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
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137439768783191808303938429927 : ((p4 ∧ (((((p1 ∨ False) ∧ p2) → False) ∧ (True → ((p1 ∧ (True → p4)) ∨ p4))) ∨ ((p4 ∧ p4) ∧ (False ∧ True)))) ∨ (True ∨ (p2 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178470907870245761850812864145 : ((((True ∧ ((p5 ∨ (p1 ∨ p4)) ∧ p2)) ∧ False) ∨ (True ∧ (p5 ∨ False))) ∨ ((p5 ∨ False) → ((((p4 → p1) → (p1 ∧ p3)) → p4) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_579733033366576905181562213633 : (((p4 → ((((((p4 → p2) ∨ p3) ∧ (p1 ∨ False)) ∨ (False ∨ ((True → p2) → p3))) ∨ ((p4 ∧ (p5 ∨ True)) → (p5 → True))) ∨ p4)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319185664417876844844257570986 : (p4 ∨ ((p2 ∨ (((True ∧ (p3 ∧ p3)) ∨ (p3 ∧ True)) ∨ (((True ∧ p5) ∧ p5) ∨ (p3 ∨ True)))) ∨ ((((False ∧ True) → p5) → False) ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609271103801915691136010585939 : ((((((False ∨ (p1 ∧ p4)) → (((True → False) ∨ ((((p4 → (p1 ∧ (p5 ∨ (p2 → p5)))) ∧ p2) ∨ p4) ∧ p2)) → p5)) ∨ True) ∨ p4) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247298289335021119761749487374 : ((False ∨ False) ∨ ((False ∧ (((p1 ∧ p4) ∨ (((p3 ∧ p4) → p5) ∨ (p5 ∧ (((False ∨ p4) → p1) ∧ (p1 → p5))))) ∧ True)) ∨ (True ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261169050607593402446640099191 : ((p4 → p4) → (True ∧ (((p5 → p3) → (((p2 → ((((p2 → p5) ∧ ((p4 → True) ∧ p5)) ∧ p5) ∨ p1)) ∧ (p4 ∧ False)) ∨ p3)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134195132088365894616574302291 : ((((p4 ∧ (p3 ∧ (p5 ∧ (True ∨ ((p4 ∨ p2) ∨ p3))))) ∧ ((True ∨ (p4 → p5)) ∧ (p1 → (False ∨ p3)))) ∨ True) ∨ (p1 ∨ (p5 → p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42212303398953710338780357964 : (((False ∧ (((False ∧ ((p1 ∨ True) ∨ False)) ∨ ((((p4 → p3) → p5) → (p3 ∧ p5)) ∨ ((p2 ∨ (False ∨ p1)) → p5))) ∧ p2)) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136830666130711327722928543745 : (((False ∧ p4) ∨ (p1 ∨ ((p1 → False) → (((p3 → (p4 ∧ (p1 ∧ p1))) → p1) ∧ (p3 ∨ ((p2 → p5) ∨ True)))))) ∨ ((p5 → p4) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655064990182361515588927881800 : (((((p3 ∧ (p4 ∨ ((p2 ∨ (p5 ∧ False)) ∨ ((((p2 ∨ (p1 ∧ (False ∨ True))) ∨ p4) ∧ (True → p1)) → p1)))) → p2) ∨ (p2 ∨ True)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246525094317520990240499188335 : ((p5 ∧ p1) ∨ (((p5 ∧ (True ∨ p5)) ∧ p3) → ((p5 → p3) → ((((p5 → p3) ∨ p1) ∧ p4) → ((((p1 ∨ p5) → False) → False) ∨ p5))))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h1.left
    let h8 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h1.left
    let h15 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h14.left
    let h17 := h14.right
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h16
    case inr h19 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40460053796843556005499522979 : ((((((p5 ∨ False) → (False ∧ p1)) → ((((True ∧ False) → (p2 ∨ p5)) ∧ ((p4 → (p1 → p2)) ∧ p4)) → (False ∨ p5))) ∨ p2) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704418361437673642392290773836 : ((((((p5 → p2) ∧ False) ∨ (p4 → (False → (p3 ∨ p5)))) → (p2 ∨ (((p4 ∧ (((p1 ∧ (p2 ∧ p5)) ∧ p2) ∧ p5)) ∧ True) ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175134629014235972767651511023 : ((p5 ∧ (((False → p3) ∧ (((False ∨ p2) ∨ ((p1 ∨ p1) ∨ False)) ∧ False)) → p5)) → (True → ((p1 → p2) → ((p3 ∨ True) ∨ (False ∧ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42350701291563922435243970107 : (((p3 ∧ ((True ∧ (p2 ∨ (p3 ∧ p5))) ∧ (p2 → ((True ∧ p2) ∧ (p1 ∨ (p2 ∨ (((p4 ∧ False) ∧ (p2 → p4)) ∨ p4))))))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_740409108601222183167351325193 : ((((p1 ∨ p3) ∨ (((p3 ∧ (False → (False ∨ (p2 ∧ p4)))) ∨ p4) → ((False ∨ False) ∨ ((p2 → p4) → (p1 → (True ∧ (False → True))))))) ∨ False) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Implications on the right can always be decomposed.
    intro h10
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h11
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179690298066683039444611487587 : ((((p3 ∨ ((p3 → ((p4 ∨ p5) ∨ p5)) ∨ (p2 ∨ True))) ∧ p2) ∧ p3) → ((p2 ∧ (p5 ∧ p4)) ∨ ((((False ∧ p2) ∧ p4) ∧ p2) → True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259626707801579486116847750641 : ((p1 → False) → ((True → (p3 ∨ ((((((True ∧ p3) ∧ (True ∨ False)) ∧ p5) ∧ False) → (((True ∨ p3) ∧ p5) ∨ p2)) → p2))) ∨ (False → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42669584580389345260323790071 : (((p4 ∨ ((p1 ∧ p5) ∨ ((p1 ∨ p4) → ((p5 → p4) ∧ (((p4 ∨ True) ∧ ((p5 ∨ ((True ∧ p2) → p3)) ∨ p5)) ∨ p1))))) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45567484004109450185808817252 : (((p2 ∨ ((p5 → p2) ∨ ((p2 ∨ p4) ∨ ((p5 → ((p4 → ((False ∨ p5) ∧ ((p2 ∧ True) ∨ (p3 → p2)))) ∧ p1)) ∧ p1)))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_17825106775799959460685534079 : (((((True ∧ ((True → p5) ∧ p3)) → (((p3 ∨ False) ∧ ((p5 ∨ (False ∨ p1)) → p1)) ∧ p1)) ∧ p5) ∨ (((True ∨ True) ∨ p4) ∨ True)) ∧ True) := by
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
theorem thm_5_vars_191767918831293216590491474434 : ((p1 ∨ (((p1 → p5) → ((p3 ∨ p5) → False)) → p1)) ∨ (p3 → (False ∨ (((p4 ∧ False) ∨ p4) ∨ (False → ((True ∨ p5) ∨ (True → True))))))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330645691661830172368808630156 : (True → (True → (p3 ∨ (p2 → ((p5 ∧ (p3 ∨ (True → (p5 → (p4 ∨ (p4 ∨ (p5 → p3))))))) → (((p4 ∨ (p4 ∨ False)) ∨ p2) ∧ p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Conjunctions on the left can always be decomposed.
  let h9 := h4.left
  let h10 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h11 =>
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h12 =>
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227658468588825078490167188927 : ((False ∧ (False → p5)) ∨ (p2 → ((((p1 ∨ (True → True)) → (p3 ∧ (p3 ∧ p4))) ∨ ((p3 ∨ p4) ∧ p1)) ∨ (p4 ∨ ((p4 → p2) → p2))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177909898224323006504537131547 : (((((p3 → p3) ∨ (p4 → (p3 ∨ (p5 → p1)))) → (p2 ∨ p2)) ∨ p4) ∨ ((((p3 → ((p2 → (p4 ∨ p3)) ∨ True)) → False) ∧ p3) → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p3 → ((p2 → (p4 ∨ p3)) ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_706696598350118613241953431539 : ((((p5 → (p3 ∨ (((p5 ∨ p3) ∧ False) → p1))) ∧ (True → ((p1 ∨ p3) ∧ (((p3 → (((p3 → p2) ∧ True) ∨ p3)) ∧ p2) → p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777196940361602940650144042761 : (((p1 ∨ ((p3 ∧ ((((p3 ∧ ((p2 → p2) → True)) → (p5 → False)) ∧ (p4 → (p2 ∧ p3))) ∧ (p3 ∨ p2))) ∧ (False ∧ (p2 ∨ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257216585247021144509724223603 : ((p2 ∨ p2) → ((p4 ∨ (p5 ∧ p5)) → ((((p1 → (p2 ∧ p2)) ∧ p3) ∧ (False ∨ ((True → p2) ∨ (p5 ∨ True)))) ∨ ((p4 ∨ p5) → p2)))) := by
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
      -- Implications on the right can always be decomposed.
      intro h5
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h7 =>
        -- One of the premise coincides with the conclusion.
        exact h4
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h11 =>
        -- One of the premise coincides with the conclusion.
        exact h8
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h16
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h18 =>
        -- One of the premise coincides with the conclusion.
        exact h15
    case inr h19 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h20
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h21 =>
        -- One of the premise coincides with the conclusion.
        exact h19
      case inr h22 =>
        -- One of the premise coincides with the conclusion.
        exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180919366132780120976183037236 : (((True ∧ p5) ∧ ((p5 ∨ ((p1 ∨ p5) ∧ ((p2 ∧ False) → p3))) ∧ p5)) → (p3 ∨ ((p4 ∨ (p4 → (False → p5))) ∧ ((p3 → False) → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h3.left
  let h7 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Implications on the right can always be decomposed.
    intro h10
    -- False on the left can always be used.
    apply False.elim h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h16
      -- Implications on the right can always be decomposed.
      intro h17
      -- False on the left can always be used.
      apply False.elim h17
      -- Implications on the right can always be decomposed.
      intro h18
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h19 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h20
      -- Implications on the right can always be decomposed.
      intro h21
      -- False on the left can always be used.
      apply False.elim h21
      -- Implications on the right can always be decomposed.
      intro h22
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679709067249321744990043320324 : ((((((False ∧ (((False ∨ (((p5 ∨ p4) ∧ p4) → (False ∨ (p4 ∨ p2)))) ∧ p2) ∨ p3)) → p1) ∨ p1) → (p4 ∨ ((p4 → False) ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45031152177190032749914313204 : ((((p2 ∨ p3) ∨ (((((p4 → p1) → (p5 → p4)) → True) → (p4 → ((p1 ∧ (True ∧ (p1 ∧ False))) ∨ (p1 ∨ False)))) ∧ p1)) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191228154061534679657927849777 : (((p4 ∨ (p2 ∨ p4)) → (p2 ∨ ((p1 ∨ p1) ∨ False))) ∨ ((p3 ∨ p3) → ((((p2 ∧ p3) ∧ (p2 → (p4 → (p2 → p3)))) → False) ∨ True))) := by
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
theorem thm_5_vars_146950440120486136191139974214 : ((((((p2 ∧ p1) ∧ p4) ∨ ((False ∧ (p4 ∨ (p2 ∧ (p3 → p3)))) ∧ ((p1 ∧ p2) ∧ p5))) ∨ p2) ∧ False) ∨ (p3 ∨ (False → (p3 ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_593004605887292553455595499251 : (((((((p5 ∨ (((p4 → (False ∧ ((False ∨ p2) ∨ (p2 ∨ (p3 → p1))))) ∨ p4) ∨ False)) → p5) ∧ False) ∨ (p1 → (p1 → p3))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147900202229793105419446455472 : ((((((p2 → (p3 → ((False ∧ p1) ∧ ((p4 ∨ False) ∧ (p5 → p3))))) ∨ p2) ∧ p2) → p4) ∧ (p2 ∧ False)) ∨ (((p5 ∨ True) ∨ p4) ∨ p2)) := by
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
theorem thm_5_vars_300832047991521049097104325786 : (False ∨ ((p2 → (((p4 ∨ (p4 ∨ p2)) ∧ p1) ∧ (((p2 ∨ p3) ∨ p3) ∨ (p4 → p2)))) → ((((p2 → p2) ∨ (False → p4)) → p2) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((p2 → p2) ∨ (False → p4)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h6
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_701700126594174438481131638901 : (((((p5 → False) → (((p2 → p4) → (False ∧ p2)) → p4)) ∧ ((((False ∧ p2) ∧ p3) ∧ (True ∧ p2)) ∨ (p2 → (p3 ∧ (p2 ∧ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136838080903493412999493977898 : (((p2 ∧ True) ∨ ((p3 ∨ ((p3 → p4) → ((False → True) → (p1 ∧ (p1 ∨ (((False → p1) ∧ p4) → p3)))))) ∨ True)) ∨ (p5 → (p2 ∨ p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1792214580772198452825987976 : ((((p2 ∨ (p5 ∧ (True ∧ p5))) ∨ p3) ∧ (((True ∧ p4) ∧ (False ∨ p2)) ∧ (((p5 → False) → p1) ∨ True))) ∨ ((True ∧ True) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_803479310402205779929517026418 : (((p3 → ((((p2 → (p5 → p2)) ∧ ((p5 ∧ (False ∨ p2)) → (p2 ∨ (False ∨ (p2 ∧ ((False ∨ (True → p4)) → p4)))))) ∨ True) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344105472371397296959242206282 : (p2 → (False ∨ ((((p1 ∧ (p1 → p5)) ∧ (((False → p2) → True) ∧ p2)) → (p4 ∨ (((p3 ∧ p4) → True) → ((p1 → p3) ∨ p4)))) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707140496209221375271545419747 : ((((((p2 ∨ (p5 ∨ p3)) → (p4 → p2)) → p2) ∨ ((p3 ∧ (p2 ∧ (((p5 ∧ p4) ∧ p3) ∧ ((p5 ∧ p2) ∧ p2)))) ∨ (p3 ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304878766734223150515492097144 : (p1 ∨ ((p1 ∧ ((((p1 ∧ ((False → p2) → ((p1 → ((True ∨ True) ∧ p5)) ∨ True))) → (True ∧ p2)) ∨ (False ∧ p2)) ∧ True)) → (p2 ∧ p2))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : (p1 ∧ ((False → p2) → ((p1 → ((True ∨ True) ∧ p5)) ∨ True))) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h2
      -- Implications on the right can always be decomposed.
      intro h8
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h9 := h6 h7
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- False on the left can always be used.
    apply False.elim h12
  -- Conjunctions on the left can always be decomposed.
  let h14 := h1.left
  let h15 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h16 := h15.left
  let h17 := h15.right
  -- Disjunctions on the left can always be decomposed.
  cases h16
  case inl h18 =>
    -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
    have h19 : (p1 ∧ ((False → p2) → ((p1 → ((True ∨ True) ∧ p5)) ∨ True))) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h14
      -- Implications on the right can always be decomposed.
      intro h20
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h18, we can now drive its conclusion.
    let h21 := h18 h19
    -- We need to get the right conjuct of h21 based on <expert-advice>.
    let h22 := h21.right
    -- One of the premise coincides with the conclusion.
    exact h22
  case inr h23 =>
    -- Conjunctions on the left can always be decomposed.
    let h24 := h23.left
    let h25 := h23.right
    -- False on the left can always be used.
    apply False.elim h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350991939768900066821199276734 : (p4 → ((p1 ∧ (((True ∨ (p2 ∧ (p1 ∧ True))) → True) ∧ (False ∨ (False ∧ ((p1 ∧ (p5 ∨ ((p4 ∧ p5) → False))) ∧ p3))))) ∨ (False → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150304765216281057543610367142 : ((p4 → ((((p1 ∧ p4) → p5) ∨ p1) ∧ (p5 ∧ ((p1 ∧ (p4 ∨ p1)) ∧ ((p3 ∧ p2) ∨ (p3 ∧ False)))))) ∨ ((p1 ∨ True) → (p5 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205552787880598380904685387192 : (((p4 ∨ p2) ∧ ((p1 ∨ False) ∨ p5)) ∨ (((p1 → p3) → ((p5 ∨ ((p4 ∧ ((p5 ∨ False) ∨ p4)) ∨ (p2 → True))) ∧ p2)) ∨ (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47581214680583351342348528696 : (((p1 → (p5 ∨ ((p3 ∨ p4) → ((p3 → (p2 ∨ ((p1 ∧ (p4 ∧ ((p3 ∨ False) ∨ False))) → False))) ∨ (p5 → p2))))) ∨ (p4 ∨ True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342685386893930913503907599041 : (p2 → (((((p1 ∧ p3) ∧ (False ∨ (p4 → p5))) ∧ False) → p1) → (True ∧ (((((p5 → p1) ∧ (p4 → p3)) ∧ (p1 ∧ p1)) ∧ p4) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_604130546630234690228688773730 : ((((p5 ∨ (p4 ∧ (p3 ∧ ((((p4 ∧ p5) ∨ (((p2 → (p2 ∧ (p5 ∨ p2))) ∧ (p2 ∨ p5)) ∧ p1)) ∨ (False ∧ p5)) ∨ p1)))) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_104918749385985746374516961853 : (((p5 ∨ (((p2 ∧ p1) ∨ ((p2 ∨ (p4 ∨ (p3 ∧ ((p1 → False) ∧ (p4 ∨ p2))))) ∧ p4)) ∧ (True ∨ False))) → (False ∨ True)) ∧ (p5 → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- False on the left can always be used.
        apply False.elim h10
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h16 =>
          -- False on the left can always be used.
          apply False.elim h16
      case inr h17 =>
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h18 =>
          -- Disjunctions on the left can always be decomposed.
          cases h5
          case inl h19 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h20 =>
            -- False on the left can always be used.
            apply False.elim h20
        case inr h21 =>
          -- Conjunctions on the left can always be decomposed.
          let h22 := h21.left
          let h23 := h21.right
          -- Conjunctions on the left can always be decomposed.
          let h24 := h23.left
          let h25 := h23.right
          -- Disjunctions on the left can always be decomposed.
          cases h25
          case inl h26 =>
            -- Disjunctions on the left can always be decomposed.
            cases h5
            case inl h27 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h28 =>
              -- False on the left can always be used.
              apply False.elim h28
          case inr h29 =>
            -- Disjunctions on the left can always be decomposed.
            cases h5
            case inl h30 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h31 =>
              -- False on the left can always be used.
              apply False.elim h31
  -- Implications on the right can always be decomposed.
  intro h32
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747170393040370221114099078409 : ((((p5 ∨ False) → ((False ∨ (p1 → (p5 ∧ (((p4 ∧ (p4 → ((p3 ∨ True) ∨ True))) ∨ (False ∨ (p4 ∧ p4))) ∧ True)))) ∧ (p2 ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179650490745089732236789761017 : ((p5 → (((False ∧ (p4 ∨ (p5 → p5))) ∨ ((p2 ∧ p3) → p2)) → p4)) ∨ ((p4 ∨ ((p3 ∧ p4) → (p4 → (p3 → p3)))) ∨ (False ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_920912470733586945555861927112 : (((((True → False) ∧ ((False → p1) ∨ ((p2 ∨ p1) ∧ (p2 → (p1 ∨ p2))))) ∨ (((p1 ∧ p2) ∧ (((p2 ∨ p1) ∧ p4) ∧ False)) ∧ p5)) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h6 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h7 := h3 h6
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h11 =>
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h12 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h13 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h14 := h3 h13
        -- False on the left can always be used.
        apply False.elim h14
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- Conjunctions on the left can always be decomposed.
    let h18 := h16.left
    let h19 := h16.right
    -- Conjunctions on the left can always be decomposed.
    let h20 := h18.left
    let h21 := h18.right
    -- Conjunctions on the left can always be decomposed.
    let h22 := h19.left
    let h23 := h19.right
    -- Conjunctions on the left can always be decomposed.
    let h24 := h22.left
    let h25 := h22.right
    -- Disjunctions on the left can always be decomposed.
    cases h24
    case inl h26 =>
      -- False on the left can always be used.
      apply False.elim h23
    case inr h27 =>
      -- False on the left can always be used.
      apply False.elim h23
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54382545821360890005024603430 : (((p3 → (True ∧ ((False ∨ (p3 ∨ p1)) ∧ p2))) ∧ (True → (((False → p5) ∧ (p3 ∨ (p3 ∨ p2))) → ((True → True) ∧ (p5 ∨ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_661250141727849130918153690228 : (((((p1 ∨ (False ∧ (True ∧ ((((p4 ∧ p3) → (True ∧ True)) → True) → ((p1 ∧ p1) ∨ (p5 → p4)))))) ∨ (p3 ∨ True)) → (p1 ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610719098622061055173443748152 : ((((((p2 ∨ (((p4 ∧ (p2 ∨ p5)) ∨ (((p3 ∨ False) → (p3 ∧ (False ∧ p3))) ∨ p1)) ∧ True)) ∨ ((False → p3) → False)) → p4) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_728340877864692140531162340493 : ((((p1 → (True ∧ p2)) ∨ (True → (((p3 → (p2 ∨ ((False → p5) → p3))) → p4) → ((p4 ∨ (p3 ∨ p3)) → (True ∧ (True → False)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113780147583119972759579042261 : (((((p1 ∨ p2) → False) ∨ (p3 ∨ (((((False ∨ p5) → True) → (p1 → p5)) ∧ (False → p4)) → (p3 ∧ p5)))) → (True ∧ False)) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135283132273680787366725538010 : (((p1 → ((True ∨ ((p4 ∨ (p3 ∨ p5)) ∧ True)) ∨ ((p1 → False) ∧ ((p2 ∧ (p3 → p3)) ∨ p4)))) → (p5 ∨ p3)) ∨ ((p2 ∧ p3) → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357873618192099923059375311416 : (p5 → (p5 ∧ ((True ∧ (((((p2 ∧ (False ∧ p3)) → (p4 ∧ p2)) → p1) → p4) ∧ p4)) → (((p2 ∧ True) ∨ (False ∨ (p1 ∨ p4))) ∧ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h2.left
  let h8 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137142817985705356719377445558 : ((True ∧ (p1 → (((p1 → (p2 → p4)) → (p1 → (True → ((p4 → p5) ∨ ((p2 ∧ p4) → p3))))) ∧ (p1 ∧ p2)))) ∨ (True ∨ (p4 → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



