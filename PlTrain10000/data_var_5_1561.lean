variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_686813918912380216534059740971 : ((((p4 ∧ ((((False ∨ (p2 ∧ p3)) ∧ ((((p3 ∨ p5) ∧ True) ∨ p2) ∨ True)) ∨ p2) ∧ p5)) → (True → ((p3 → p3) → (False ∨ p5)))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h16 =>
          -- Conjunctions on the left can always be decomposed.
          let h17 := h16.left
          let h18 := h16.right
          -- Disjunctions on the left can always be decomposed.
          cases h17
          case inl h19 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h7
          case inr h20 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h7
        case inr h21 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h7
      case inr h22 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
  case inr h23 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180830446539968949177375403753 : (((True → (p4 ∨ p2)) ∧ (((False ∧ p2) ∨ ((p2 ∧ p5) ∨ p2)) → False)) → ((((p1 ∧ True) ∧ p2) → (p3 ∨ p5)) ∧ ((True ∧ p3) → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h9 : ((False ∧ p2) ∨ ((p2 ∧ p5) ∨ p2)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h10 := h8 h9
  -- False on the left can always be used.
  apply False.elim h10
  -- Implications on the right can always be decomposed.
  intro h11
  -- Conjunctions on the left can always be decomposed.
  let h12 := h11.left
  let h13 := h11.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h1.left
  let h15 := h1.right
  -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
  have h16 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h14, we can now drive its conclusion.
  let h17 := h14 h16
  -- Disjunctions on the left can always be decomposed.
  cases h17
  case inl h18 =>
    -- One of the premise coincides with the conclusion.
    exact h18
  case inr h19 =>
    -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
    have h20 : ((False ∧ p2) ∨ ((p2 ∧ p5) ∨ p2)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h19
    -- We have shown the premise of h15, we can now drive its conclusion.
    let h21 := h15 h20
    -- False on the left can always be used.
    apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174100611766083150039121690236 : ((((p2 → (True → p4)) ∨ (((p3 → p2) ∨ p2) → (False ∧ True))) ∧ (p4 ∧ p4)) → ((((p5 ∧ (p2 → p3)) ∧ (p1 ∧ p3)) → p4) ∨ True)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h3.left
    let h9 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638948210469046136416855727980 : (((((p3 ∧ ((p5 ∨ p3) ∨ False)) ∧ ((((p3 ∧ p2) ∧ (p2 → (p5 ∨ p1))) ∧ (p5 ∨ (p3 ∨ p5))) ∧ (p3 ∨ (p1 → p2)))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_629355724563014576667643272869 : (((((((False ∨ p4) ∨ ((((False ∨ False) ∧ (p5 → True)) ∧ (p5 ∧ ((p3 → (False ∨ p4)) ∧ (p2 ∧ True)))) ∨ False)) → p3) ∨ p5) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138583893194722397941139926057 : ((((((p1 ∨ p5) → p5) → (((p5 ∨ (True ∨ (False → p2))) ∨ (p1 ∧ (p4 → False))) ∧ (p2 → p2))) → p3) ∧ True) → ((p2 ∨ p3) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (((p1 ∨ p5) → p5) → (((p5 ∨ (True ∨ (False → p2))) ∨ (p1 ∧ (p4 → False))) ∧ (p2 → p2))) := by
    -- Implications on the right can always be decomposed.
    intro h5
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
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318894953459113559630533880468 : (p4 ∨ ((p3 ∧ (((False ∧ (p3 ∨ p3)) ∨ (p3 → (((p3 ∧ p2) ∧ ((p2 → p3) ∧ (p1 ∨ True))) ∨ p2))) ∧ p3)) ∨ (True ∨ (p2 → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_599061619618265703215315316926 : (((((p5 ∨ p4) ∧ (((((p2 → (False ∨ ((p5 ∨ (p2 ∧ (True ∨ p1))) → p2))) ∨ (p3 ∨ False)) ∧ (p3 ∨ False)) ∨ p2) ∧ p2)) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638615137899482806916143724140 : (((((p3 → ((p2 ∧ False) ∧ (p5 → False))) ∨ ((False ∧ ((False ∨ (p1 → p5)) → p4)) → ((False ∨ p5) ∨ ((p3 ∨ p3) ∨ True)))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349937232453837028433649686666 : (p4 → (((((p5 ∨ True) → (False ∨ (p5 ∧ ((((False ∧ True) ∧ (p5 → ((True ∧ (p3 ∨ p4)) ∧ p2))) ∨ False) ∨ p3)))) ∧ p5) ∧ p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258365629570155449855580660197 : ((p5 ∨ False) → ((((p5 ∨ p4) ∧ (True ∧ p5)) ∨ p2) → (p1 → (((p1 → (p5 ∧ False)) → (False ∧ ((True ∧ (p5 → p3)) → False))) ∨ p2)))) := by
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
    cases h5
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h11
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
        have h12 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h3
        -- We have shown the premise of h11, we can now drive its conclusion.
        let h13 := h11 h12
        -- We need to get the right conjuct of h13 based on <expert-advice>.
        let h14 := h13.right
        -- False on the left can always be used.
        apply False.elim h14
        -- Implications on the right can always be decomposed.
        intro h15
        -- Conjunctions on the left can always be decomposed.
        let h16 := h15.left
        let h17 := h15.right
        -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
        have h18 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h3
        -- We have shown the premise of h11, we can now drive its conclusion.
        let h19 := h11 h18
        -- We need to get the right conjuct of h19 based on <expert-advice>.
        let h20 := h19.right
        -- False on the left can always be used.
        apply False.elim h20
      case inr h21 =>
        -- False on the left can always be used.
        apply False.elim h21
    case inr h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h6.left
      let h24 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h25 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h26
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- We want to use the implication h26 based on <expert-advice>. So we show its premise.
        have h27 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h3
        -- We have shown the premise of h26, we can now drive its conclusion.
        let h28 := h26 h27
        -- We need to get the right conjuct of h28 based on <expert-advice>.
        let h29 := h28.right
        -- False on the left can always be used.
        apply False.elim h29
        -- Implications on the right can always be decomposed.
        intro h30
        -- Conjunctions on the left can always be decomposed.
        let h31 := h30.left
        let h32 := h30.right
        -- We want to use the implication h26 based on <expert-advice>. So we show its premise.
        have h33 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h3
        -- We have shown the premise of h26, we can now drive its conclusion.
        let h34 := h26 h33
        -- We need to get the right conjuct of h34 based on <expert-advice>.
        let h35 := h34.right
        -- False on the left can always be used.
        apply False.elim h35
      case inr h36 =>
        -- False on the left can always be used.
        apply False.elim h36
  case inr h37 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h38 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h37
    case inr h39 =>
      -- False on the left can always be used.
      apply False.elim h39



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_592711429757405274506413111511 : (((((((False ∨ p3) → (p2 ∨ ((p1 ∧ (p5 ∨ (p1 ∨ (p3 ∨ (p5 ∧ (p4 ∧ False)))))) ∧ True))) ∧ p4) ∧ (p1 ∨ (p1 ∧ p4))) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114953657111332693923339056465 : (((p2 ∧ ((p4 → ((p3 ∨ p3) ∧ (True → (p5 ∨ True)))) → (p3 ∨ p5))) → (p5 → (((p4 → (True → False)) → False) → p4))) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65607834817037658388296202219 : ((p4 ∨ (((p4 ∧ p4) ∨ (p1 ∨ ((p3 → p5) → ((p5 ∨ p3) ∧ (((p2 ∨ (p1 → p2)) ∨ (False ∨ False)) → (False ∨ p3)))))) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_9440936367918125677857657596 : ((((p2 ∨ ((p5 ∧ True) → p4)) → ((p5 ∧ (p2 → ((p1 → ((p4 ∧ p5) ∨ (p3 ∨ True))) → p4))) ∨ ((p5 ∨ False) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136047050449423567661699815190 : (((p4 → (((p4 ∧ p2) ∧ p4) → (False ∧ (p2 ∧ p3)))) → ((True ∨ (p5 ∨ p3)) ∧ ((p3 → p1) ∨ (p2 ∨ True)))) ∨ (p2 → (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774011897733244113345433869677 : (((False ∨ ((True ∧ ((p2 ∨ ((p1 ∨ (p5 ∧ (False ∨ p1))) ∧ p3)) ∧ (True ∧ (True → (True ∧ (p5 ∨ (True ∨ p5))))))) ∧ (True ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173530710916563585830727960656 : ((((((p3 ∧ p4) ∨ False) ∨ (False → True)) ∧ (((p3 ∧ p3) ∨ p1) ∨ p1)) ∧ p1) → ((False ∨ p2) → (((p1 → p4) ∨ (False → False)) ∨ p2))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h1.left
    let h6 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h13 =>
          -- Disjunctions on the left can always be decomposed.
          cases h13
          case inl h14 =>
            -- Conjunctions on the left can always be decomposed.
            let h15 := h14.left
            let h16 := h14.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h4
          case inr h17 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h4
        case inr h18 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h4
      case inr h19 =>
        -- False on the left can always be used.
        apply False.elim h19
    case inr h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h21 =>
        -- Disjunctions on the left can always be decomposed.
        cases h21
        case inl h22 =>
          -- Conjunctions on the left can always be decomposed.
          let h23 := h22.left
          let h24 := h22.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h4
        case inr h25 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h4
      case inr h26 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245429959715464184298557306645 : ((p2 ∧ p4) ∨ ((p1 ∧ (p1 → ((p4 → p2) ∨ p5))) ∨ (p3 ∨ ((p1 ∨ p1) ∨ (p3 → (p5 ∨ ((p4 ∨ True) ∨ (p3 ∧ (p1 → p5))))))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_28060677620574306040545968 : (((False → ((p2 → (True → p1)) ∧ ((p4 ∧ (p2 ∧ p4)) ∨ (False ∨ True)))) ∧ p2) → (((p2 ∨ True) → (p5 → p4)) ∨ True)) := by
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
theorem thm_5_vars_184927058410965202711334950070 : (((False ∨ (p5 ∧ p3)) ∨ (((True ∧ p4) ∨ p2) ∨ (p2 ∨ p1))) ∨ ((p4 → ((True ∧ (p2 ∨ p4)) ∨ p2)) ∨ (p2 ∧ ((p1 ∨ p3) → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_752748022006949469418974871 : (((p1 ∨ (p5 → p4)) ∨ (p5 → (p5 ∧ (p1 → ((p3 ∨ ((((p5 ∧ p2) ∧ p2) ∨ False) ∧ (p5 ∧ p3))) ∨ (True ∨ p4)))))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_127107034939302602839756498561 : ((False ∨ (p3 ∧ (((p3 → ((p4 → (p2 ∧ ((p4 ∨ (p5 → p4)) → (True ∨ p3)))) ∧ (p1 ∧ p5))) ∨ p1) ∧ (p2 → False)))) → (p1 ∨ p2)) := by
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
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h9 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h10 := h8 h9
      -- We need to get the right conjuct of h10 based on <expert-advice>.
      let h11 := h10.right
      -- We need to get the left conjuct of h11 based on <expert-advice>.
      let h12 := h11.left
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h13 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319490939863007313486636122756 : (p4 ∨ (((p2 ∨ (p3 ∨ p3)) ∨ ((p4 ∧ (p3 ∨ p4)) ∧ (p1 → p1))) → (((p5 ∧ False) ∨ (p5 → (((p3 → p2) ∨ True) ∨ p4))) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h4
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h7
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
        -- Implications on the right can always be decomposed.
        intro h9
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h11.left
    let h14 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h16
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h17 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h18
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308689253524905536977566667508 : (p2 ∨ ((p1 ∨ (p3 ∧ (p3 ∨ (False ∨ ((p5 → True) ∧ (((True ∨ (p4 ∨ (p5 ∧ (p3 ∧ p5)))) ∧ (True ∧ False)) ∨ (p5 ∧ p3))))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_880900472652485694392419965998 : ((((((False ∨ (False → (((p2 ∨ p3) → False) → (p3 ∧ p4)))) → ((p4 ∧ ((p2 ∧ p4) → p1)) ∧ (p3 ∧ p2))) ∨ p2) ∨ (p2 ∧ p3)) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h4 : (False ∨ (False → (((p2 ∨ p3) → False) → (p3 ∧ p4)))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h5
        -- Implications on the right can always be decomposed.
        intro h6
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- False on the left can always be used.
        apply False.elim h5
        -- False on the left can always be used.
        apply False.elim h5
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h7 := h3 h4
      -- We need to get the right conjuct of h7 based on <expert-advice>.
      let h8 := h7.right
      -- We need to get the right conjuct of h8 based on <expert-advice>.
      let h9 := h8.right
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- One of the premise coincides with the conclusion.
      exact h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- One of the premise coincides with the conclusion.
    exact h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_627812171818048506714460077805 : (((((((((p4 → p4) ∨ ((p1 ∨ (p1 → p2)) → p4)) ∨ p2) → (p2 ∧ p1)) ∨ (((p1 → p1) → (p1 ∧ p5)) ∧ False)) ∧ p4) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134556228245845663905082459699 : ((((p2 ∧ (((p2 → (p4 ∨ p5)) ∧ p5) → (((p4 ∧ (p2 ∧ False)) ∨ (p3 ∨ (True ∨ p4))) ∧ p1))) → p3) → p4) ∨ (False → (p5 ∧ p2))) := by
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
theorem thm_5_vars_306009643915914447991366991415 : (p1 ∨ ((False ∧ ((p2 ∧ p3) ∧ False)) ∨ (True → (p4 → (((p1 → (False ∨ (((p2 ∨ (True ∨ p1)) → p5) → p5))) → p4) ∨ (p1 → False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347138316822773560209041589291 : (p3 → (((((p4 ∧ True) ∧ p4) ∧ (True ∨ p4)) ∨ (p2 → ((p3 → False) ∨ p1))) → (((p2 ∧ p2) ∨ True) ∨ ((p4 ∨ (False ∨ True)) ∨ p2)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h12 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_806277745933402863068744721534 : (((p4 → ((((p4 ∧ (((p3 ∨ p1) ∧ False) ∧ (p1 ∧ p4))) → p4) → ((p1 ∨ p2) ∧ (((p3 ∨ True) ∧ p2) → (p2 → p5)))) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702828268431140904765306068006 : (((((p2 → ((p1 → p5) → True)) ∧ (p3 → (p4 ∨ p5))) ∨ (((False → ((True → False) → (p5 ∨ p4))) ∧ p1) → (p2 ∨ (True ∧ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255851652610836547209614949545 : ((True ∨ p1) → ((p4 ∧ ((p3 ∨ (((p1 → (True ∨ p3)) ∧ ((p5 → True) ∧ ((p5 → p1) ∧ (p1 ∨ p1)))) → p1)) → (p4 → p2))) ∨ True)) := by
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
theorem thm_5_vars_792372746800996319905412986191 : (((True → ((((p2 ∨ p3) ∧ ((p5 ∧ (p3 ∨ p3)) ∨ (p3 ∧ p4))) → (p4 ∧ True)) ∨ ((p1 ∧ True) → ((p3 → p2) → (p3 ∧ p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336337782527127828436047164671 : (p1 → (((p1 ∨ (False → p4)) → ((p2 ∨ True) → ((p4 → (((p1 ∧ (False ∨ ((False ∨ (p4 → p2)) ∨ p1))) ∧ p5) → p3)) ∨ True))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h8 =>
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
theorem thm_5_vars_52722229905488856516290101209 : (((((p2 ∨ p3) ∧ (p5 ∨ ((p2 → ((p1 ∧ p4) ∧ True)) → p1))) ∧ True) → ((p1 → p3) → ((False ∨ (p3 ∨ True)) ∨ (p1 ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_143325352987888304279076082456 : ((p4 → ((p4 ∧ ((True ∧ ((((False ∨ False) ∨ (p5 → False)) ∨ p2) ∨ False)) ∧ True)) ∨ (p4 ∨ ((True ∨ p5) ∨ True)))) → ((True → p4) → p4)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346314447156326743840241282486 : (p3 → ((((((p2 ∨ p5) ∨ p2) ∨ (p3 ∨ ((p5 → p5) → p2))) → ((p4 ∧ False) ∧ (p5 ∧ (p1 ∨ p3)))) ∧ (True ∧ p4)) ∨ (p4 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258423106724563698751806441461 : ((p5 ∨ p1) → (((p1 → (((p1 ∨ (p3 → p1)) ∨ p2) → False)) ∨ True) ∨ ((((((False ∨ p4) ∨ (p3 ∨ p2)) ∧ p1) → p3) ∧ p4) → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_16778708307821803903434720748 : (((((((p2 → (p1 → True)) ∧ (p4 → p1)) ∨ p5) → p5) ∨ (((p1 ∨ True) ∨ (p1 ∧ (p3 → p5))) → True)) ∨ (p2 → (p2 ∧ True))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114901496944307298042433986622 : (((p3 → (p4 ∧ (((False → ((p1 → True) ∨ p1)) ∨ (p1 ∨ False)) ∨ p5))) ∨ ((((p3 ∨ p1) ∧ False) ∧ (p5 ∧ p3)) ∨ p2)) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215132282551021849000149757125 : (((p4 → p1) → (p5 ∧ p4)) ∨ ((p4 → (p5 ∧ p1)) → (False ∨ ((p3 ∨ (((p1 → ((p5 ∧ p2) → False)) ∧ p4) → p4)) ∨ (p4 ∧ p5))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134412159743151198574486528978 : (((p2 → (((((p5 → p3) ∧ (True ∧ ((p3 ∧ True) ∨ (True → (p4 ∧ p3))))) → (p3 → False)) → p5) → p1)) ∨ True) ∨ ((p2 ∧ p1) ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193928269193178780662675017891 : ((p1 ∨ (p3 ∨ ((p3 ∨ p2) ∧ (p2 → (p3 → p3))))) → ((p5 → True) → (p1 ∨ (((p5 → p1) ∧ (True ∧ (p5 ∨ p2))) ∨ (False → p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- False on the left can always be used.
        apply False.elim h11
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h13
        -- False on the left can always be used.
        apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44881080137114177074224930894 : (((((p5 ∧ p3) ∨ True) → ((p4 ∨ p2) → (((p4 → p2) ∧ p5) ∧ (False ∧ ((p4 → ((p2 ∨ p2) ∧ False)) ∨ (p3 ∨ p4)))))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_740227372402577143449490282934 : ((((False ∨ p5) ∨ (True → (((p4 → (True ∨ True)) → (p3 ∧ (False ∧ (((p1 ∧ True) ∧ True) → p5)))) ∨ (((p4 ∧ True) → p3) → False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698965702600655910972817321287 : ((((p5 ∧ (True ∧ ((False ∧ (p2 → (p2 → p3))) ∧ (p3 ∨ p3)))) ∨ ((p5 ∧ ((p3 → p1) ∨ False)) ∨ (p1 ∨ ((p2 ∧ False) → False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192367142164501287863774788793 : (((p3 → (False ∨ (((p2 → p3) ∧ p5) → p4))) ∧ p4) → (((True ∨ (True → p4)) → ((True ∨ ((p2 ∧ p3) ∧ p4)) ∧ p3)) ∨ (p4 ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669012853597822044588335038778 : ((((((p2 → (True ∧ ((p1 → (p3 → (p4 → True))) ∨ ((p2 → p4) → ((p4 → p1) ∧ p5))))) ∧ p1) → p3) ∨ ((p3 → p3) ∨ p4)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49432358570345283658525035209 : ((((((True ∧ ((((((p3 ∨ p1) ∨ p2) ∨ False) → True) → p3) ∧ False)) ∨ (False ∨ (p5 → p4))) → p2) ∨ False) → ((p2 ∨ p2) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233215705983091353712357645814 : ((p5 ∧ (p2 → False)) → (p1 → ((((((p2 ∨ p1) → False) ∧ (p3 ∨ (p2 ∨ p3))) ∧ p4) ∧ (p5 → p3)) ∨ (p4 ∨ ((p5 → p1) ∧ True))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178519914566951934478558429380 : ((((True ∧ ((False → (p3 ∨ p1)) ∧ p5)) → p3) → ((False ∧ p5) ∧ True)) ∨ ((p3 ∧ (p3 ∧ p4)) ∨ (((p3 → (False ∧ True)) → p3) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40619489066727961907748698229 : (((((True ∨ ((True ∧ (((True → (p2 ∨ (p1 → p1))) → p2) ∧ p4)) ∧ (p4 → (False ∨ (p5 → (p1 ∧ p1)))))) ∨ p5) → p3) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206529182895093075965122590361 : ((True → (((p3 ∧ p1) ∨ p5) ∨ p3)) ∨ ((p4 → (False ∨ (p4 ∨ True))) ∨ (((True → ((True ∨ True) ∧ (True ∧ (True ∧ False)))) ∧ p5) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305865944147957917273591819082 : (p1 ∨ ((((p5 ∨ p5) ∨ (p2 ∧ p2)) ∨ p5) ∨ ((((p2 ∧ False) → ((False ∧ True) → (p3 ∨ ((p3 → True) → (p3 → p5))))) ∨ p2) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_636246666968738198769529417872 : (((((p1 ∨ ((((True → p3) ∧ p5) → p5) ∨ (((p4 → (p4 ∧ p3)) ∧ False) → p3))) ∨ ((p3 → False) ∧ ((p3 → p3) ∧ p3))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323242207402987776683225396314 : (p5 ∨ (((p4 ∨ p3) ∧ ((p4 ∨ False) ∧ ((p5 ∨ (p5 ∧ (((p2 ∨ p4) ∧ True) → p5))) → ((p4 ∨ p3) ∨ (True → False))))) ∨ (True ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171942284878375515981575035634 : ((((((p5 ∧ ((p5 → p1) ∧ p3)) → True) → p3) ∧ (p1 → False)) ∧ (p3 ∨ True)) ∨ (((False ∧ ((p3 → False) → (True ∨ p2))) → p4) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_768316803839398176578095519240 : (((p5 ∧ ((p2 ∨ ((((p1 ∨ (p3 ∨ (p4 ∨ False))) → (p2 ∨ p3)) ∧ (p2 ∨ ((False → False) → p1))) → p1)) ∨ ((p1 → p1) ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45787268863889184584794044679 : (((p1 → ((p3 → ((p5 ∧ (True ∧ (((((p1 → p2) ∨ False) ∨ (p5 ∨ p3)) → False) ∧ p2))) ∨ (p3 ∧ (p4 ∧ False)))) → p5)) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41242813976432003246339106575 : ((((((p2 ∧ (((((p3 ∧ p4) → p3) ∨ p5) ∨ False) ∧ (False ∧ p1))) → (True ∨ p5)) ∧ p3) ∨ ((False ∨ p2) ∧ (p1 → p2))) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670682335798912318110233676931 : (((((p1 → p5) → ((p5 → False) ∧ ((p3 → (((True → (((False → p2) ∧ p1) ∧ p2)) ∨ p4) → p1)) ∧ p3))) ∨ (p2 → (p3 → p3))) ∨ p4) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60917824690908908562378218106 : ((False ∧ ((((p1 ∨ p1) ∧ (True → (p5 → ((False ∨ p3) → (((p1 → (p5 ∧ p1)) ∧ p1) ∨ (p1 ∧ p2)))))) ∨ (p5 ∧ p1)) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42288304978986269417647975542 : (((p1 ∧ (p4 → (False ∨ ((p2 ∨ ((False ∨ (p5 ∨ p5)) ∨ p4)) ∨ ((((p2 ∧ p2) → p1) → ((p4 → p2) → p3)) ∨ False))))) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_781340779847669632320373400715 : (((p2 ∨ (p1 ∧ (p5 ∧ (p3 ∨ (True → (((((p3 ∧ p3) ∧ (False → False)) → False) ∧ (((p3 ∧ p3) ∨ p2) → (p4 ∨ p2))) → p4)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53297157061503427850438620062 : (((p2 ∨ ((((True ∧ p4) → (True ∨ p5)) ∨ p5) → (p3 ∧ False))) ∨ (p4 → ((False ∨ ((((p5 ∨ p3) → p3) → True) ∧ p3)) → p4))) ∨ p4) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206469371456396515979953832767 : ((p4 ∨ (True → (False ∨ (p2 ∨ p2)))) ∨ ((p1 → ((p2 ∧ (((p2 ∨ p1) ∧ p5) → p3)) ∨ p1)) ∨ ((False ∨ (True → p2)) ∧ (p3 ∧ p4)))) := by
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
theorem thm_5_vars_218429259585713927460609989803 : (((p2 ∧ p2) → (True ∨ False)) → ((p1 ∨ (((((((p1 ∧ p4) → p2) ∧ False) ∨ True) ∨ p1) ∧ p1) ∧ True)) ∨ (False → (p4 ∨ (False → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670102898750973597779796209948 : (((((p2 ∧ (((p2 → True) ∧ p3) → p1)) ∧ (((p4 → p2) ∧ ((p4 → (p3 ∨ p2)) ∨ p5)) ∨ (p2 ∧ p4))) ∨ ((False ∧ p2) ∨ True)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_171866682466016774766903387784 : (((p1 ∧ (((p3 ∨ True) → ((p3 ∨ p1) → True)) ∨ ((p1 → p5) ∨ False))) → p4) ∨ ((p3 ∧ p5) ∨ (True ∨ ((False → (p2 ∨ p1)) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668829756840813255031813677929 : (((((((p3 ∨ False) ∨ ((p2 ∧ p5) → (True ∧ False))) ∧ (((p3 → (p2 → (True ∨ p3))) ∨ False) ∨ False)) ∨ p5) ∨ ((True ∧ True) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314769889879139592496471428261 : (p3 ∨ ((((p1 ∨ (p4 ∧ (((False ∨ p2) ∨ p4) ∨ True))) ∨ (p5 → p5)) → p2) → (True → (((p4 ∨ True) → (p2 ∧ p1)) ∨ (p5 → p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307533816693191467295472721268 : (p1 ∨ (True → (p1 → ((((p3 → p3) ∨ ((p2 → (p1 → ((p4 ∧ p1) ∧ p5))) ∧ p1)) → ((p3 → p5) ∨ ((p1 → False) ∨ True))) ∨ p4)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111477110342194963131028476181 : (((p1 → (p4 ∨ (((p2 ∧ (p4 → p3)) → True) → ((p3 ∧ (p1 → (p1 → (p2 ∨ ((False ∧ p4) ∧ False))))) ∧ p1)))) ∧ p1) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60502657264423699713666102153 : ((True ∧ (((((p2 ∨ p4) → p1) ∨ False) ∨ ((True → (((p5 ∧ p5) → (p2 ∨ (p5 → p3))) ∧ p1)) ∨ ((p4 ∧ p2) ∧ p3))) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682823515582681812762746861062 : (((((p1 ∧ (p1 ∨ p3)) ∨ ((True ∨ (((False ∨ p2) → ((p4 ∨ False) → p3)) ∨ p2)) ∧ False)) ∧ (False ∧ (p2 ∨ ((True → True) → False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305750839799516538179671580116 : (p1 ∨ ((p1 ∨ (((False ∧ p2) → (p2 ∨ p2)) ∨ p2)) ∧ (False ∨ (False ∨ (((p1 → p4) ∨ (p4 ∨ True)) → ((p5 ∧ True) ∨ (p3 → True))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
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
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133782532207893932120506313387 : ((((p1 → ((p5 ∨ p5) ∧ p5)) → ((((p5 → True) → p5) ∨ (((p3 ∨ (p4 ∧ p5)) → True) → True)) → p4)) ∧ p4) ∨ (p3 → (p4 ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_778229154019397174547310782421 : (((p1 ∨ ((True → True) → (p5 → (((False → (p5 ∧ True)) → ((False ∧ ((False → p5) ∨ ((p5 ∧ p5) ∧ (True ∧ p2)))) ∨ p4)) ∨ p5)))) ∨ False) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48944818678837120238572801980 : (((((p2 ∧ p2) ∨ (((((p4 ∨ p2) → p1) → (p4 ∧ p5)) ∧ p5) ∧ ((p4 ∨ False) → (False → p3)))) ∧ p5) ∨ ((p4 ∧ True) ∨ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351302821816698621306054025908 : (p4 → (((((False → (p5 ∧ False)) → (p3 ∨ (p1 → p1))) → p2) ∧ ((False ∨ p3) → ((p3 → (p2 → False)) → p5))) → ((p5 ∨ False) → p2))) := by
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
    let h5 := h2.left
    let h6 := h2.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : ((False → (p5 ∧ False)) → (p3 ∨ (p1 → p1))) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h10 := h5 h7
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_154147269183946945945408152670 : (((((True → p1) ∧ (((p1 ∧ (((p2 → True) ∨ False) → p5)) ∨ False) ∧ (p4 ∧ p5))) ∨ False) ∨ True) ∧ (True → (True ∨ ((False → p2) → p5)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_944244704038960198273084581546 : ((((((p5 → p3) ∧ p2) ∧ True) ∨ (((p4 ∧ p3) ∧ p5) ∧ ((p2 ∨ p4) → ((p4 ∨ False) ∧ ((p3 ∧ p2) ∧ ((p2 ∧ p5) ∨ p4)))))) → p2) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h14 : (p2 ∨ p4) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h12
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h15 := h9 h14
    -- We need to get the right conjuct of h15 based on <expert-advice>.
    let h16 := h15.right
    -- We need to get the left conjuct of h16 based on <expert-advice>.
    let h17 := h16.left
    -- We need to get the right conjuct of h17 based on <expert-advice>.
    let h18 := h17.right
    -- One of the premise coincides with the conclusion.
    exact h18
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53806603762049195500311639940 : ((((p1 ∨ (p1 ∧ ((p3 ∧ True) → (False ∧ True)))) → False) ∨ ((((p5 → (p3 → p5)) → p3) ∨ (p5 → (False → (True ∨ True)))) ∨ False)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698171066868556251548665586415 : ((((((p2 ∨ ((False ∨ (True ∧ p1)) ∧ (p1 → p2))) → False) → p3) ∨ ((p2 ∧ ((p1 ∨ (p5 ∨ (True → p5))) → (p1 ∧ p3))) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199668800836268112688692095530 : ((((p3 ∧ p1) ∨ (True ∨ (False → True))) → False) → ((True → (((p3 → True) ∨ p3) ∧ p4)) → (((p3 ∨ (False ∨ (p4 ∨ p1))) → p5) ∧ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h5 : ((p3 ∧ p1) ∨ (True ∨ (False → True))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h6 := h1 h5
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h11 : ((p3 ∧ p1) ∨ (True ∨ (False → True))) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h12 := h1 h11
        -- False on the left can always be used.
        apply False.elim h12
      case inr h13 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h14 : ((p3 ∧ p1) ∨ (True ∨ (False → True))) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h15 := h1 h14
        -- False on the left can always be used.
        apply False.elim h15
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h16 : ((p3 ∧ p1) ∨ (True ∨ (False → True))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h17 := h1 h16
  -- False on the left can always be used.
  apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615546542984505463417991356137 : ((((((True ∨ (p1 → p1)) ∧ (p3 ∨ (p1 ∨ (False ∧ (p4 ∧ (p1 → (p2 ∧ True))))))) → ((False ∧ p5) ∨ (p1 → (False → p3)))) ∨ False) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h10
        -- Implications on the right can always be decomposed.
        intro h11
        -- False on the left can always be used.
        apply False.elim h11
      case inr h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- False on the left can always be used.
        apply False.elim h13
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h17
      -- Implications on the right can always be decomposed.
      intro h18
      -- False on the left can always be used.
      apply False.elim h18
    case inr h19 =>
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h21
        -- Implications on the right can always be decomposed.
        intro h22
        -- False on the left can always be used.
        apply False.elim h22
      case inr h23 =>
        -- Conjunctions on the left can always be decomposed.
        let h24 := h23.left
        let h25 := h23.right
        -- False on the left can always be used.
        apply False.elim h24
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_82371372398557435247020322611 : ((((p4 → (p3 → ((p3 ∧ p5) ∨ (False → p4)))) → (p4 ∧ ((p3 ∧ ((p1 → p5) → p1)) ∧ False))) ∧ (((p5 ∧ p1) ∧ p2) → False)) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p4 → (p3 → ((p3 ∧ p5) ∨ (False → p4)))) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h4
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42240700318940811297004991001 : (((False ∧ (p3 ∧ (((((p5 → ((((p5 → (p1 ∨ p1)) ∨ p3) ∧ (p2 ∨ p5)) ∧ p3)) ∨ p1) ∧ p1) → (True ∧ False)) ∨ p3))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64135374738649470101414831333 : ((False ∨ ((p4 ∨ ((p2 ∧ p1) ∨ p1)) → (((False ∧ (p2 ∧ (p3 → (p2 ∧ (True → (p4 ∧ True)))))) ∨ p5) ∨ (p5 → (p5 ∨ p4))))) ∨ False) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167476525755554267380821198196 : (((p5 → (p4 ∨ ((((p3 → (True ∨ (False ∨ False))) ∨ p5) → True) ∧ (p2 ∨ p5)))) → p4) → (((p2 ∧ ((p2 → p5) → True)) → p4) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 → (p4 ∨ ((((p3 → (True ∨ (False ∨ False))) ∨ p5) → True) ∧ (p2 ∨ p5)))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707914074062296731014839358149 : ((((p5 ∧ (((p3 ∨ p3) ∨ (p4 ∧ p4)) ∧ p4)) ∨ (False → (p2 ∨ (p5 → (p1 → ((p1 → p4) → ((p5 → (p4 ∨ True)) ∨ p4))))))) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_257188555118012867683528907828 : ((p2 ∨ p2) → ((p1 → ((p5 → False) ∨ ((((False ∧ p5) → p3) → p1) → ((p4 ∧ (False → (((p5 ∧ True) ∨ False) ∧ p1))) ∧ False)))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63074544060309366885201568254 : ((p5 ∧ (((((p2 ∧ ((True → (p3 → p3)) ∨ p5)) ∧ (((p1 ∧ (p5 ∨ p5)) ∧ (p4 ∨ False)) → (p5 ∧ True))) → p4) ∨ p3) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308331222149387122466073662530 : (p2 ∨ (((((p4 → ((True ∧ (p1 ∨ p5)) ∨ ((((p3 ∨ True) ∨ (p4 → (p1 → False))) ∧ (p5 ∧ p3)) ∧ p5))) ∧ True) ∨ False) ∧ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55422631659471394764545424855 : ((((p5 ∧ (True → (p2 ∨ p2))) ∨ p1) → (p5 → (p2 ∨ (((((p1 → (p5 ∧ True)) ∨ p3) → (p3 → (p2 → p1))) ∨ p1) ∨ True)))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702890359600029898586508196390 : (((((True ∧ ((p5 ∨ True) ∨ p5)) → ((p5 ∧ p4) ∧ p5)) ∨ (((True ∨ False) ∧ (False ∧ (p2 → (False ∧ (p1 ∨ p2))))) ∨ (False → p5))) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_729866564997107619154983775390 : (((((p1 ∧ p1) → p4) → (p2 → ((p4 ∧ p3) → (((p1 ∧ p2) → p4) ∧ ((True ∧ ((p2 → p5) ∨ False)) ∨ (p1 → (p4 ∧ p4))))))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h3.left
  let h8 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h7
  -- Conjunctions on the left can always be decomposed.
  let h9 := h3.left
  let h10 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h11
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h9
  -- One of the premise coincides with the conclusion.
  exact h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207736311251579977943754611711 : (((p4 ∧ (p5 → (p2 ∧ False))) → p1) → (((True ∨ p4) → True) ∧ ((p4 → False) → (p3 ∨ ((p4 ∧ p2) ∨ (p1 → (p5 → (False → False)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_649395642225112749776179941991 : (((((p5 → (p3 → (((p3 ∧ p4) ∧ ((True ∨ True) → (((((p5 ∨ True) → True) → p2) → p5) ∧ p2))) → True))) → p1) ∧ (p4 ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



