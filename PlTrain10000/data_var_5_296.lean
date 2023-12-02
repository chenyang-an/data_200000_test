variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339017772378274979126475073337 : (p1 → (True ∧ (((p4 ∧ (((p5 → p2) ∧ False) ∨ (p4 ∨ p5))) ∨ (p4 ∨ True)) ∨ (False ∨ (p4 ∧ ((True → (True ∧ True)) → (p2 ∨ True))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217652367400251932689400236178 : ((((False ∨ p5) → p4) → False) → (((True ∧ ((p1 ∨ (p2 ∨ p3)) ∧ p4)) ∧ (True ∨ (False ∨ (((p1 ∧ p1) ∧ (p4 ∧ False)) → p2)))) → p3)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h10 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h11 : ((False ∨ p5) → p4) := by
        -- Implications on the right can always be decomposed.
        intro h12
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- False on the left can always be used.
          apply False.elim h13
        case inr h14 =>
          -- One of the premise coincides with the conclusion.
          exact h8
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h15 := h1 h11
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- False on the left can always be used.
        apply False.elim h17
      case inr h18 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h19 : ((False ∨ p5) → p4) := by
          -- Implications on the right can always be decomposed.
          intro h20
          -- Disjunctions on the left can always be decomposed.
          cases h20
          case inl h21 =>
            -- False on the left can always be used.
            apply False.elim h21
          case inr h22 =>
            -- One of the premise coincides with the conclusion.
            exact h8
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h23 := h1 h19
        -- False on the left can always be used.
        apply False.elim h23
  case inr h24 =>
    -- Disjunctions on the left can always be decomposed.
    cases h24
    case inl h25 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h26 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h27 : ((False ∨ p5) → p4) := by
          -- Implications on the right can always be decomposed.
          intro h28
          -- Disjunctions on the left can always be decomposed.
          cases h28
          case inl h29 =>
            -- False on the left can always be used.
            apply False.elim h29
          case inr h30 =>
            -- One of the premise coincides with the conclusion.
            exact h8
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h31 := h1 h27
        -- False on the left can always be used.
        apply False.elim h31
      case inr h32 =>
        -- Disjunctions on the left can always be decomposed.
        cases h32
        case inl h33 =>
          -- False on the left can always be used.
          apply False.elim h33
        case inr h34 =>
          -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
          have h35 : ((False ∨ p5) → p4) := by
            -- Implications on the right can always be decomposed.
            intro h36
            -- Disjunctions on the left can always be decomposed.
            cases h36
            case inl h37 =>
              -- False on the left can always be used.
              apply False.elim h37
            case inr h38 =>
              -- One of the premise coincides with the conclusion.
              exact h8
          -- We have shown the premise of h1, we can now drive its conclusion.
          let h39 := h1 h35
          -- False on the left can always be used.
          apply False.elim h39
    case inr h40 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h41 =>
        -- One of the premise coincides with the conclusion.
        exact h40
      case inr h42 =>
        -- Disjunctions on the left can always be decomposed.
        cases h42
        case inl h43 =>
          -- False on the left can always be used.
          apply False.elim h43
        case inr h44 =>
          -- One of the premise coincides with the conclusion.
          exact h40



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_588983857758941782495680584500 : (((((True → (False ∨ (p1 ∧ (p2 ∧ (p3 ∨ (p5 ∧ ((p3 → ((p3 ∧ (((p5 ∧ p1) ∧ p2) ∨ False)) ∨ p4)) ∨ p2))))))) ∨ p4) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260725433796782596185502835675 : ((p3 → p4) → ((True → (p2 ∨ (p2 ∨ ((((p4 ∧ (p3 → p1)) ∧ True) ∨ p2) ∧ ((p1 ∨ True) ∨ False))))) ∨ (p5 → ((True ∧ p5) ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_868468408113204063272797421172 : (((((p4 → True) → (((p3 ∨ True) → (((p1 ∨ (((False → p3) ∧ p5) ∧ p3)) ∧ p3) ∧ (False ∧ (p4 → (False ∧ p4))))) → p1)) → p2) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p4 → True) → (((p3 ∨ True) → (((p1 ∨ (((False → p3) ∧ p5) ∧ p3)) ∧ p3) ∧ (False ∧ (p4 → (False ∧ p4))))) → p1)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : (p3 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- We need to get the left conjuct of h7 based on <expert-advice>.
    let h8 := h7.left
    -- False on the left can always be used.
    apply False.elim h8
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112912501757719937669630841551 : ((((p3 ∨ p2) ∨ (((False → (True ∨ (((p3 ∨ p5) ∨ (p1 ∨ p5)) ∧ (p4 → (p2 ∧ True))))) → p3) ∨ (p2 → p1))) → False) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173288454683122384787109201948 : ((p1 → (((p4 → (((p3 → (p2 → (p5 ∨ p1))) → p3) → False)) → p5) ∨ p1)) ∨ ((((p3 ∧ p1) ∨ (False → (False → p4))) ∧ p5) → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53266193244678417505386691534 : (((True ∧ ((p1 ∧ (False ∨ (((p1 ∧ True) ∧ p4) ∧ p2))) ∧ p4)) ∨ ((p3 ∧ p4) ∧ (p4 ∧ ((p4 ∨ p1) ∨ (p4 ∧ (p4 ∨ p5)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213433542332364782709970591824 : (((p4 ∨ (p3 ∧ False)) ∧ p1) ∨ (((True → ((p4 ∧ True) ∧ (p1 ∨ p1))) ∨ p4) ∨ ((True ∨ (True ∨ ((p2 ∨ False) ∨ (p3 ∧ p4)))) ∨ p4))) := by
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
theorem thm_5_vars_53948052775427042117342122200 : (((p4 → ((p4 ∧ ((p3 ∨ (p3 → p5)) → False)) ∨ False)) ∨ ((((p3 → p5) → p4) → (False → (((p1 ∨ False) ∧ p3) ∧ p2))) ∧ True)) ∨ p2) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_641197508595929167439596611117 : (((((p3 ∨ False) ∨ (((((p5 ∧ (p3 → p2)) ∧ (True → (p2 → True))) ∨ (p3 ∨ (True ∧ p5))) ∧ True) → ((p5 ∨ p2) → p4))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_623784978106467738301822032952 : ((((p1 ∨ (((p2 ∧ ((p5 → (False ∧ p2)) ∨ True)) ∨ p3) → ((((True ∨ p4) → p1) → (p1 ∧ p5)) → ((p2 → p5) ∧ False)))) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_351723910934995756728491408214 : (p4 → (((((((p1 ∧ p3) → p2) → False) ∧ ((p5 → p2) ∨ p1)) → p3) → p2) ∨ ((p1 → True) → ((True ∨ (p1 ∨ (p4 → p3))) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1537213391601177736032594013 : (((p1 ∧ p1) → ((p1 ∨ p3) → (((p2 ∧ (((p1 → (False → (True ∨ (p4 ∨ p3)))) ∨ True) → p3)) ∨ p4) ∨ True))) ∨ (p3 → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h1.left
    let h8 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340645919087293553424205052804 : (p2 → ((p5 ∨ (((((p1 ∧ (p3 → False)) ∨ False) ∧ p3) ∧ ((p3 → p1) → ((p3 → p3) ∨ p4))) ∨ (True ∧ ((p2 ∨ p1) ∨ False)))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164721205022039533749491701147 : ((((((p3 → ((p4 → (False ∨ p3)) ∨ p2)) → p1) ∧ ((True ∨ p3) ∨ p3)) → p4) ∨ False) ∨ (p5 ∨ ((False → p2) → ((p1 ∨ p2) → True)))) := by
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
theorem thm_5_vars_346859019490053257281316364809 : (p3 → (((((p3 ∨ (((p5 → ((p3 ∨ True) → (False ∨ p2))) ∧ False) ∨ p2)) → p3) → p1) ∨ p3) ∧ ((p4 → ((False ∧ p1) ∨ p4)) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191619575441765718666605828521 : ((p3 ∧ (p2 ∧ ((p3 ∧ p4) ∧ (p1 ∨ (p3 ∨ p2))))) ∨ ((True ∧ True) ∨ ((p2 → (p2 ∨ (False ∧ p5))) → (p5 ∧ ((p1 ∧ p4) ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115854899833980930496235416226 : (((p4 ∨ (p1 ∨ (p5 ∧ False))) ∧ (False ∨ ((((p1 ∨ p5) ∧ True) → ((p1 ∧ p1) ∧ (p3 ∧ ((False ∨ p3) → p4)))) ∨ p2))) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181580946524349510379164871826 : ((p1 → ((((p2 → (p5 → p2)) ∨ (False → False)) ∨ (True ∨ p1)) → p2)) → (((False ∨ ((p3 ∨ (p3 ∨ p5)) ∧ (True → False))) ∨ True) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41462162608536559964896592281 : ((((p2 ∧ ((p3 → (p5 ∧ (p4 ∨ True))) → (True → (p5 → p3)))) ∧ ((((p5 → (p2 → p1)) ∨ (True ∧ p5)) ∧ p2) ∧ True)) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_649816926942022020749271850902 : (((((p2 ∧ (((p4 ∧ p3) ∧ (((p3 ∨ (False ∧ p1)) → p3) → ((p1 → True) → (False ∧ False)))) → False)) → (p3 → False)) ∧ (p4 ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185365390339501827316184240999 : ((p4 ∧ (p5 → ((p4 ∨ p5) ∨ (((False ∨ p5) → p2) → p3)))) ∨ ((p4 → ((((p5 ∨ (p3 ∧ p1)) ∧ p4) → p4) → p5)) → (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308652770719410066983002333462 : (p2 ∨ ((p2 ∧ (((p2 ∨ p1) ∧ (p1 → (False → (((p3 → (False ∧ (p4 → p5))) ∧ p3) ∧ (p4 ∧ (p3 ∧ True)))))) ∧ (p1 ∨ p2))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231391127964233566294214904585 : (((p1 → True) ∨ p4) → ((p2 ∨ ((True → p1) → p2)) → ((p4 ∨ ((((p4 ∨ ((p4 → p1) ∨ p3)) ∧ p1) ∧ (p3 ∨ p2)) → p2)) ∨ True))) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
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
theorem thm_5_vars_664245363511424595508770504013 : ((((p1 ∨ (((p2 ∨ ((p5 ∨ False) ∨ (p4 → p4))) → (p3 → p4)) ∧ ((p4 ∨ (p2 ∧ ((True ∨ False) ∨ False))) ∨ p5))) → (p4 ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_266179746871723553516516230717 : (True ∧ (p4 → (((True ∧ (False ∨ ((((True ∧ ((((False ∧ p5) ∨ p4) ∨ p4) → p5)) → p4) ∨ ((p3 → p1) ∨ p5)) → False))) ∨ p3) ∨ p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151457388674468650226187774109 : (((((((p4 ∧ False) ∨ ((p5 ∨ (p5 ∧ (True → p5))) ∨ p3)) → (p1 → p1)) ∨ p3) ∨ p4) ∨ (p5 → p4)) → (p1 ∨ (True → (p1 ∨ True)))) := by
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h5
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h7
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58220055899474814680918987306 : (((p4 ∧ p3) ∧ (((False ∧ ((p4 ∨ (((p1 ∧ ((((p1 → p5) → p4) ∧ p1) → p3)) ∨ (p5 ∧ p4)) ∧ p3)) ∨ p1)) ∧ True) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250702816545372197222192316949 : ((p1 → False) ∨ ((p3 ∨ (p2 ∧ ((p5 ∨ (False ∧ (p5 ∧ p5))) ∨ (((p2 → (False → (p5 → p1))) ∨ p1) ∨ p4)))) ∨ ((False → True) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_41145202155752824826049132947 : ((((((p3 → p3) → ((p2 → (p1 ∨ p1)) ∧ p3)) ∨ ((p3 ∨ p1) ∨ ((True → p4) ∧ (False → True)))) ∨ (p1 ∨ (True → p4))) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208879854350923768518067759094 : ((p4 ∧ (p2 ∧ (True → (p3 → p3)))) → (p3 ∨ (True ∧ (((((False → p4) ∧ (True ∨ (True ∨ p1))) → (p1 ∧ False)) ∨ True) ∨ (True → p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115790746359062339114658575094 : (((((True ∧ False) ∨ False) ∨ p5) ∧ (p5 ∨ ((p5 ∧ (((((p4 ∨ False) ∨ p3) ∧ (p5 → True)) ∨ (False → p1)) ∧ p2)) ∨ True))) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748499200463538736589594222005 : ((((p3 → True) → (((p3 ∨ p4) ∧ ((((False ∧ p2) ∧ (p5 ∨ p5)) → ((p1 → True) → p4)) ∧ (((p5 → p2) ∧ p4) ∧ p5))) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187242027090331896136958822696 : ((True ∧ ((p3 ∧ (p3 ∧ (((p3 → p3) → p2) ∨ p2))) → True)) → (p1 ∨ (((False → (((False ∨ False) → p2) ∧ p1)) → p1) → (p2 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_797299060919448310808867404409 : (((p1 → (((((False ∧ (p5 ∧ p1)) ∨ (p1 → (p3 ∨ p3))) ∨ (((p2 ∧ p1) ∧ (False ∨ p5)) ∨ (p4 → p3))) ∨ (True ∧ False)) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41637331388241971710778431044 : ((((False → (((False ∧ False) → (p3 ∨ p4)) ∨ False)) → (p2 ∧ ((((True → False) ∧ ((False ∧ (True ∨ True)) → p2)) ∨ p5) ∨ p5))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62655967476068507994086878139 : ((p4 ∧ (((((p4 ∨ (p5 → (True ∨ p5))) → ((((p2 ∨ True) ∧ (p3 ∧ (p4 ∨ False))) ∧ p4) ∧ p4)) ∧ p1) ∧ (p3 ∧ p2)) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58979327632546661795263980006 : (((p2 ∧ p5) ∨ (((True ∧ (True → ((((p1 ∧ p2) ∨ ((p4 ∧ p1) → p2)) ∨ (True ∨ p3)) ∧ (False ∧ p2)))) → (p5 ∨ p3)) ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351218877652591412890259784496 : (p4 → ((((p5 → (p4 ∧ ((p3 ∧ (p5 ∨ (p2 ∧ p3))) → (p2 ∨ ((p1 ∧ False) ∨ (True → p5)))))) ∨ p4) → p2) ∨ (False → (p2 ∧ True)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231595578762513183067769018889 : (((True ∧ p1) → False) → ((((((p4 ∨ p1) → (p2 ∧ (p2 ∧ (p5 → p3)))) → False) ∨ ((p3 ∧ p4) → ((p2 ∧ p5) ∨ p3))) ∨ False) ∨ p5)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185772668561629086456825032552 : ((p4 → ((False ∨ (p5 ∨ p5)) → ((p2 → p2) → (p4 ∧ p1)))) ∨ ((p3 ∧ ((p5 ∧ (((p2 ∧ p4) ∨ p4) → p3)) ∧ (p3 → False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112506609214342618139475758024 : (((((((p5 ∧ p3) → ((p3 ∧ (p1 ∧ (p5 ∧ (True → p4)))) ∧ p1)) → ((False ∧ (p3 ∧ p1)) ∧ False)) ∧ p3) → p1) → p1) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319541229646852747748878228054 : (p4 ∨ (((((p3 → False) → (p2 ∨ p4)) ∨ (p5 ∧ False)) → False) ∨ ((((True ∨ True) ∨ (p1 ∨ p1)) ∨ ((p4 ∧ False) ∧ False)) ∧ (p1 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208200555220461428693065359757 : (((True → (True ∧ False)) → (p2 ∧ p5)) → ((((p1 ∨ p5) → ((p2 ∧ (False → (p1 → (p1 → True)))) ∧ p3)) ∨ (False → (p5 → p3))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205933994008577759017768335771 : ((False ∧ ((p5 ∧ p3) ∧ (p3 ∧ p2))) ∨ (p2 ∨ (True ∨ ((p5 ∧ p4) → ((p2 ∨ (p2 → False)) ∧ ((p4 ∨ (p4 ∧ (p4 ∧ False))) ∧ p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156984317598610391810963276536 : ((((((p3 ∧ (p3 → p1)) ∧ True) ∨ p5) ∧ ((p4 → (p3 ∨ (p2 ∨ p5))) ∨ (p3 ∨ True))) ∨ p5) ∨ (False → (p4 → (p2 ∧ (p5 → False))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44783274957460495706997537443 : ((((p4 → ((False ∨ p4) ∨ p4)) → (((((True ∧ p5) ∧ p4) ∨ (((p4 ∨ p1) → (True ∨ p5)) ∨ (p5 ∨ False))) ∧ p1) ∧ p1)) → p1) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p4 → ((False ∨ p4) ∨ p4)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37959274929403768552278174809 : ((((((((((p1 → (p3 → p1)) ∧ (p4 ∧ p2)) → False) ∨ (False → False)) ∧ (False ∧ p1)) ∨ (p4 → True)) ∨ p4) ∨ (p3 → p1)) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227931081034102793106808092345 : ((p3 ∧ (False ∧ p2)) ∨ (((p1 ∨ (p3 ∨ (((p5 ∧ p2) → (p2 → True)) ∨ (p4 ∧ (p3 → True))))) ∨ ((False → p2) ∧ False)) ∨ (p1 ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301607439241707536933083838733 : (False ∨ (((p2 ∧ p5) → p1) → ((p5 → ((((((p5 ∧ p5) → p2) → (p3 ∨ p2)) → p4) ∨ p2) ∧ p4)) → (((p5 → p4) ∨ p5) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_942967714651456370998810259557 : (((((p5 → False) ∧ (p3 ∧ True)) ∧ (((p1 ∨ (False → (True → (p2 → ((p4 → (((p5 ∨ True) → False) ∨ p2)) ∨ p1))))) ∧ p5) ∧ p2)) → p1) ∧ True) := by
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
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h3.left
  let h9 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h12 =>
    -- One of the premise coincides with the conclusion.
    exact h12
  case inr h13 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h14 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h11
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h15 := h4 h14
    -- False on the left can always be used.
    apply False.elim h15
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206550861499477350578862564215 : ((True → (False ∧ ((p5 ∨ p1) ∨ p1))) ∨ ((((p4 ∨ (p5 ∧ (True ∧ (p4 ∨ p4)))) → (p1 ∧ False)) → ((p3 → False) → False)) ∨ (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112765453819270999276202092550 : ((((p4 → (p5 ∧ ((p5 ∧ p1) → (p2 → (p1 ∧ True))))) ∨ ((p5 ∨ ((((p3 ∨ True) ∨ False) → True) ∨ p4)) ∨ p3)) → p4) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307184217755096536158773605066 : (p1 ∨ (p1 ∨ ((p1 → ((((((True → (True ∨ p5)) ∧ (p3 ∨ p4)) → ((((p1 → p1) ∨ p2) → p5) ∧ p3)) → p3) → p3) ∧ p2)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148373872120933059120835143937 : ((((((p1 ∨ (p1 ∨ ((True ∧ p2) ∨ False))) → False) → (p4 ∨ p2)) → p1) ∨ ((p2 ∨ p1) → (p1 ∧ False))) ∨ (p2 → (True → (p2 ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314442357315169056224273243170 : (p3 ∨ ((True → (((p2 ∧ (((p1 → True) → p4) → p3)) ∧ ((p5 → True) → False)) ∨ ((p2 ∨ p4) ∨ p3))) ∨ ((p1 ∧ p1) ∨ (p4 → p4)))) := by
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
theorem thm_5_vars_189873992559917247512626357864 : ((p1 → (p2 → (((p5 ∧ p5) ∧ False) → (p1 ∨ p2)))) ∧ (((((p4 → p2) → p1) ∧ p5) ∨ p3) ∨ (((True ∧ False) → (p2 → p3)) ∨ p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- False on the left can always be used.
  apply False.elim h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h8
  -- Implications on the right can always be decomposed.
  intro h9
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346312729371336300152048037326 : (p3 → (((p4 → ((((p5 ∨ p3) ∨ p2) → ((p2 ∨ p4) → p1)) ∨ (((p2 ∧ ((p4 ∨ p3) → p1)) ∨ p4) → p2))) → p5) ∨ (p3 ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721871736846700194554470900705 : ((((p4 ∨ ((p1 → False) → p3)) → (((((p3 → p4) ∨ (True ∧ False)) → (p2 → ((p5 → False) ∧ True))) ∨ p1) → ((False ∧ p4) ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_102871554549565052935163231598 : ((((((True ∨ p1) ∧ (p2 ∧ (((True ∨ ((False ∧ p1) → (p1 ∨ p4))) ∧ (p1 ∨ p1)) ∧ p2))) ∧ p2) → (p1 ∧ p3)) ∨ True) ∧ (False ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_734827240308065750745426317147 : ((((p2 ∨ p1) ∧ (True ∧ ((((False ∨ (((p1 → False) ∨ (False → (p3 → False))) ∧ (True ∧ True))) → ((p3 ∨ p4) ∨ True)) → p1) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178154801457490550907697332333 : ((((p3 ∨ (True ∧ p2)) → ((p3 → (False ∧ p4)) ∧ (False ∧ p4))) → p2) ∨ (((False → (p2 ∧ (p1 ∨ (p2 → p1)))) ∨ (p1 → p5)) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_339619162046752194437904727551 : (p1 → (p2 ∨ ((((p5 → ((p3 → (p3 ∧ p3)) → (p5 ∨ (True ∧ p5)))) ∨ p1) ∨ (p2 ∨ (False ∧ (p5 ∨ p4)))) → ((True → False) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- False on the left can always be used.
      apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_763353083674374653605678030085 : (((p3 ∧ ((True → p5) → (((False ∨ (((False → True) → (p2 ∨ (True ∧ p3))) ∨ p3)) ∧ (((p5 → p4) ∨ (False → False)) → p1)) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207870818615316885263389254981 : ((((p3 → p2) ∨ True) ∧ (p2 ∧ p3)) → (p2 → (((p5 ∧ False) → (p5 → True)) ∧ ((p4 → ((p5 ∧ p1) ∨ p4)) ∧ (False ∨ (p5 → p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h7.left
    let h13 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- Conjunctions on the left can always be decomposed.
  let h14 := h1.left
  let h15 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h14
  case inl h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h15.left
    let h18 := h15.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h19
    -- One of the premise coincides with the conclusion.
    exact h19
  case inr h20 =>
    -- Conjunctions on the left can always be decomposed.
    let h21 := h15.left
    let h22 := h15.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h23
    -- One of the premise coincides with the conclusion.
    exact h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748870648363488819321589126341 : ((((p4 → p1) → (((False ∨ (((p2 ∨ False) ∨ (p1 ∨ p2)) → p4)) ∨ p2) ∨ (((p4 ∨ p3) → ((p1 ∨ False) ∧ p3)) → (True ∨ p5)))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232729218676925099957886143883 : ((p1 ∧ (True → p4)) → ((p5 ∨ ((True ∨ ((((p4 ∧ p4) ∧ p1) ∨ True) → p5)) ∧ ((p2 → False) → ((False ∧ True) ∨ p3)))) ∨ (True → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134887559729385139110641800971 : (((p4 → (((((p4 ∧ p5) ∨ True) → (((p2 ∨ (p1 ∧ p2)) → (p5 ∧ p2)) → p5)) ∧ (True → p1)) → p5)) → p2) ∨ ((p4 ∨ p4) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136386209522632331618382044045 : ((((False ∨ True) → (p4 → p3)) ∨ (p2 ∧ (p5 → (p4 ∧ (((True → (p1 → p4)) ∨ False) ∧ (p3 ∨ (p5 ∨ p5))))))) ∨ (p1 ∨ (True ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63034352303496854968737643307 : ((p5 ∧ (((((((((p5 ∨ p5) ∧ p1) ∧ p1) → (((p4 ∨ p2) → p3) ∧ (p4 ∧ p5))) ∧ (p5 ∧ True)) ∨ p3) ∧ True) ∨ p1) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_628731739096143251419313172892 : (((((False → (((p5 → ((True ∨ p2) → p4)) → (p4 ∧ ((p5 ∨ True) → p4))) ∨ (((False → p4) ∨ (False ∧ p4)) → p4))) ∧ p3) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153610416769430091180796059012 : ((False → (p5 → (((True ∧ p5) → p3) ∧ (((((p1 ∧ p4) → (False ∧ (True ∨ p1))) ∧ p2) ∧ True) ∧ True)))) → ((p3 ∧ (p1 ∨ False)) → p3)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_765166500688892920213834165550 : (((p4 ∧ ((p4 ∧ (((p3 ∧ (p2 ∨ (p5 ∨ ((((p2 ∧ False) ∧ p4) → False) ∧ True)))) ∧ ((p2 ∨ True) ∨ p5)) ∧ p4)) ∨ (True ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330723102653177645643369491683 : (True → (p1 → (((p4 ∧ p2) ∨ ((((((True ∧ p1) ∧ True) → ((p3 ∨ p3) ∨ (False ∨ (p5 ∨ p1)))) → p4) → p4) ∨ (p1 → p1))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50856854203619263149874784112 : (((((p3 ∨ (((p1 ∧ (p1 ∧ p1)) → (False → p4)) → (p2 ∨ p4))) ∨ (p2 → True)) ∨ p5) ∧ (((p4 ∧ False) ∧ p2) ∨ (False → p4))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_781129400331597740092698415450 : (((p2 ∨ ((True → p3) ∨ (((((((p5 ∧ (((p2 ∨ True) ∧ p1) → (p2 → p1))) ∨ p2) ∨ p3) → p3) → (p1 ∨ p1)) → p1) ∨ True))) ∨ p4) ∧ True) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68986753613264905962035940144 : ((p5 → (((((p3 ∨ p5) → ((((((True → p3) ∧ p5) → p4) ∨ p5) ∧ (((p1 ∨ p1) ∧ False) ∧ p3)) → p1)) → p3) ∨ True) ∧ True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_166815440793241574709136267455 : ((((True → (((False → p3) ∧ ((False ∧ p2) → (True ∧ p5))) ∧ (p4 → p2))) ∧ p1) ∧ p3) → (p4 → ((p3 ∧ (p2 ∨ (True ∧ p5))) ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h7.left
  let h10 := h7.right
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h11 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h12 := h9 h11
  -- We need to get the right conjuct of h12 based on <expert-advice>.
  let h13 := h12.right
  -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
  have h14 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h13, we can now drive its conclusion.
  let h15 := h13 h14
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h15
  -- Conjunctions on the left can always be decomposed.
  let h16 := h1.left
  let h17 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h18 := h16.left
  let h19 := h16.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157294897634117323209457452089 : ((((p3 ∧ p4) → ((p3 ∧ (((p2 ∨ (False ∨ p2)) → True) ∧ (True ∨ (p2 ∨ p2)))) → False)) → p2) ∨ (True ∨ (((p5 ∧ p2) ∨ False) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204201788502858872817007657008 : (((((p1 → p3) ∨ False) → p5) ∧ p2) ∨ ((True ∧ p2) ∨ (((p1 ∨ True) ∨ ((p5 ∨ p2) → ((p4 ∨ ((True → p4) ∧ p4)) ∧ True))) ∨ p1))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160869198556775031061368407800 : (((True → (p5 ∧ (True → False))) ∧ (((p2 ∨ False) ∧ p2) ∧ ((p2 → p3) ∧ ((p3 → p5) → p5)))) → (p1 ∧ ((p2 → (False → p4)) → False))) := by
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
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h5.left
    let h10 := h5.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h11 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h12 := h2 h11
    -- We need to get the right conjuct of h12 based on <expert-advice>.
    let h13 := h12.right
    -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
    have h14 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h13, we can now drive its conclusion.
    let h15 := h13 h14
    -- False on the left can always be used.
    apply False.elim h15
  case inr h16 =>
    -- False on the left can always be used.
    apply False.elim h16
  -- Implications on the right can always be decomposed.
  intro h17
  -- Conjunctions on the left can always be decomposed.
  let h18 := h1.left
  let h19 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h20 := h19.left
  let h21 := h19.right
  -- Conjunctions on the left can always be decomposed.
  let h22 := h20.left
  let h23 := h20.right
  -- Disjunctions on the left can always be decomposed.
  cases h22
  case inl h24 =>
    -- Conjunctions on the left can always be decomposed.
    let h25 := h21.left
    let h26 := h21.right
    -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
    have h27 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h18, we can now drive its conclusion.
    let h28 := h18 h27
    -- We need to get the right conjuct of h28 based on <expert-advice>.
    let h29 := h28.right
    -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
    have h30 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h29, we can now drive its conclusion.
    let h31 := h29 h30
    -- False on the left can always be used.
    apply False.elim h31
  case inr h32 =>
    -- False on the left can always be used.
    apply False.elim h32



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157083341165088393002640915164 : (((p4 ∨ ((p5 → (((True → True) ∨ (p5 ∨ ((p3 ∧ p1) ∧ p1))) ∧ (p2 → p5))) → p4)) ∨ True) ∨ ((p4 ∧ (p1 → p5)) → (p1 ∧ p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64891066457896508584617576238 : ((p2 ∨ ((((p1 → (((p2 ∨ p1) ∧ (p2 → (p3 → p4))) → p3)) → False) ∧ ((True → p5) → (False → p5))) ∨ (p4 → (p4 ∨ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307617573753840317764782701945 : (p1 ∨ (p1 → (((p2 ∧ ((False ∧ ((p5 ∨ (p3 ∨ p5)) ∨ p5)) ∨ (True ∨ (p5 → p2)))) ∨ (p4 → (True ∨ (p4 ∨ True)))) ∨ (p5 → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166509852250869756355727806448 : ((p4 ∨ (((((((p2 → p4) → p3) ∧ ((p1 → p3) ∨ False)) → p2) ∧ p2) ∨ p5) → p4)) ∨ ((((True ∧ (False ∨ True)) → False) → p3) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∧ (False ∨ True)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159525057517933403662397263484 : (((True ∧ ((((((p5 → p1) → (p3 → p3)) ∧ p5) ∧ False) → ((True ∧ True) ∧ True)) ∨ p2)) ∧ True) → ((p4 ∨ (p3 → p4)) ∨ (p5 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
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
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1816531443272942001685547466 : ((p5 ∨ (((p5 ∨ p3) → (p2 ∨ (p4 ∨ ((p5 → (p1 ∨ p2)) ∧ ((p2 ∨ p4) ∨ p1))))) ∧ (p3 → p5))) ∨ (p4 → (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60421384937344867938205034044 : (((p4 → p2) → (((p1 → (p1 → p1)) → p2) ∨ (p2 → ((p4 ∧ (p3 → True)) ∧ (((p2 → (False ∧ False)) ∧ p3) → (False ∧ p4)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616660197543067760428628456601 : (((((p5 ∨ (((p4 → False) ∨ ((p4 ∨ p4) ∧ p5)) → False)) ∧ (p2 ∧ ((((p5 ∧ (p3 → True)) ∨ (p5 ∨ p4)) ∨ p1) → p2))) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190735320962750859783112006564 : ((((p2 → False) → ((p2 ∨ True) → p5)) ∧ (p3 ∨ p3)) ∨ (((((p1 → p3) ∨ (p2 → True)) → (p1 → (p5 ∨ p3))) → p2) ∨ (True ∧ True))) := by
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
theorem thm_5_vars_704184103631128359135848272986 : (((((((False → p2) ∨ p1) → (p3 ∧ False)) ∨ (p1 → p2)) → (((p3 ∨ p5) → (p4 → False)) ∨ ((((False → p1) ∧ True) ∧ p1) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45061359363335681975622174133 : ((((p3 → p4) ∨ (((p1 → p3) ∧ p2) ∨ ((p2 → (p4 ∨ ((((True → p3) ∨ p3) → (p4 → p5)) → p5))) → (False → False)))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190892527602825294319450869055 : (((p2 ∧ (p3 → ((p2 ∨ p4) ∧ p4))) → (True ∧ p3)) ∨ ((p3 → p3) ∨ ((p5 ∨ False) ∧ (True ∧ (((True → (p5 → p1)) → False) ∧ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245189171261322469099876598027 : ((p2 ∧ False) ∨ ((((p1 ∧ p1) ∨ p4) → p5) → ((p1 ∨ p5) → (((p1 ∨ (p5 ∨ (False → (p4 ∨ p1)))) ∧ p5) ∨ (p1 ∨ (p1 ∧ p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39299649842537316383396581707 : (((p1 ∧ ((p4 ∨ p3) ∧ (((p3 ∧ (p3 → (p4 → p1))) ∧ ((((False ∧ False) → (False → p5)) → (True → p1)) → True)) ∨ p5))) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180255424350645532292347510560 : (((p2 ∨ ((p4 ∧ False) ∧ ((p4 ∨ False) ∨ ((p4 ∨ p3) ∧ True)))) → p1) → (((p3 → ((p3 ∧ p3) ∧ ((p5 ∨ p3) → p2))) ∨ p2) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261569741378073960248873696240 : ((p5 → p4) → (((p5 → p1) → ((p2 ∨ (((p3 → p2) → (False → p5)) ∨ (p5 → False))) ∧ (p1 ∨ ((False ∨ p5) → p3)))) ∨ (p4 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309700120965561492289273043307 : (p2 ∨ (((((p2 → (p2 ∧ p5)) ∧ p2) ∨ True) → ((p5 ∧ (p2 ∨ (((False ∨ True) → p3) ∧ True))) ∧ (False ∧ p3))) → (p1 ∧ (p5 ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p2 → (p2 ∧ p5)) ∧ p2) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- False on the left can always be used.
  apply False.elim h5
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : (((p2 → (p2 ∧ p5)) ∧ p2) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247745472718857088262172774920 : ((p1 ∨ False) ∨ ((p4 ∨ p4) ∨ ((p5 → (p3 ∨ p5)) → (((True → True) ∨ p2) → (True ∧ (((False → True) → (True → False)) → (p1 → p2))))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h5 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h6 : (False → True) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h8 := h3 h6
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h10 := h8 h9
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- One of the premise coincides with the conclusion.
    exact h11



