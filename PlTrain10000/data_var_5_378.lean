variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44651116779897496751922024930 : ((((((p3 ∨ p2) → False) ∨ (p2 ∧ p3)) ∨ ((p1 ∨ (((p3 ∨ ((p1 ∧ True) ∨ p2)) ∨ p5) ∧ (p1 ∧ (p1 → p2)))) ∨ p5)) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198827443104758243677846878647 : ((p1 → ((p2 ∨ (p5 ∧ p3)) ∧ (p4 ∧ p5))) ∨ (p4 ∨ ((False ∧ (p2 → ((p2 ∨ False) ∨ False))) ∨ (((True ∧ p2) ∧ (False → False)) ∨ True)))) := by
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
theorem thm_5_vars_40984220671150370216573570439 : ((((p2 ∧ ((((p3 ∨ (p3 → p4)) ∧ (p1 ∨ (p3 ∧ (p4 → (p2 → p5))))) → (p3 → p2)) ∨ (p2 → p3))) ∨ (p5 → p1)) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729938924767064725215532991094 : (((((p4 ∧ False) → p2) → (False ∨ ((((p3 ∧ (False ∧ ((p2 ∨ ((p2 → p3) ∧ False)) ∧ p3))) → p4) ∧ (True ∨ p1)) → (p2 ∨ True)))) ∨ p3) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_762609011423806317758670848739 : (((p3 ∧ (((((p5 ∧ (((p1 ∨ p4) ∧ p5) → (p5 ∨ p1))) ∨ False) ∧ p5) ∨ p4) ∨ ((p4 ∨ (p1 ∨ (False ∧ p3))) ∨ (True ∨ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612537591471140391082622688561 : ((((((p4 ∨ (p5 ∨ ((p1 → p4) → (((((False ∨ (p4 ∧ (p5 ∧ p1))) ∨ False) ∧ p5) ∨ False) ∧ p3)))) ∨ False) ∨ (p1 ∨ True)) ∨ False) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_125339919808472521104811580581 : (((p1 ∨ (True ∨ False)) → (((p3 ∧ (p1 ∧ True)) ∨ ((p5 ∧ (p5 ∨ (((p3 ∨ p2) ∨ True) ∧ (p3 ∧ False)))) → True)) ∧ False)) → (p5 ∧ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 ∨ (True ∨ False)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : (p1 ∨ (True ∨ False)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263380165858433086922826556353 : (True ∧ (((((p3 → (p3 → True)) → (True → ((False ∧ (True ∨ p5)) → (True ∧ ((False ∧ p5) → p1))))) ∧ True) → p3) ∨ (p3 → (p3 ∨ p2)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113309038182510114998761098988 : ((((p3 ∨ ((p5 ∨ p4) → p3)) ∨ ((p2 → (p3 ∨ (((((p3 ∧ p1) ∧ p2) → False) ∨ True) ∧ True))) ∨ False)) ∧ (p3 ∨ True)) ∨ (p4 → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337393692688859124085237822529 : (p1 → ((p3 ∨ ((((p4 ∧ (p1 ∧ p4)) ∧ ((p2 ∨ (p5 ∧ p1)) ∧ p3)) ∧ p3) ∧ ((False → p5) → (p3 → p5)))) ∨ (False ∨ (p5 → p1)))) := by
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
theorem thm_5_vars_748113643830141022255495810773 : ((((p1 → p3) → ((p1 ∨ ((False ∧ (p5 ∨ (p1 ∧ False))) ∨ (p1 ∧ ((False ∨ p2) ∧ (((p4 ∨ (True ∧ True)) ∧ p1) ∨ p2))))) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61326505929761843131390663158 : ((False ∧ (p5 → (((p1 ∧ ((((p3 ∧ p1) ∨ (False ∨ p4)) → ((p3 → p3) ∧ (False ∧ False))) → False)) → (p1 → True)) → (p4 → False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134685628605679745043837396529 : ((((((p3 ∧ False) ∨ p1) ∧ (True ∧ p5)) ∨ ((((p5 ∨ p2) → p4) ∨ p5) → (((p4 → p3) ∨ False) ∧ True))) → p1) ∨ (True ∨ (p5 ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38175501855628904819156129893 : (((((p5 ∧ p4) ∧ (((((p4 ∨ p5) ∨ ((p1 ∧ p1) → (False ∨ p2))) → p3) → p2) → (p1 ∨ p3))) ∨ ((p5 ∧ p3) → p3)) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607207275946713315385095008005 : ((((((((p2 ∨ p5) ∨ p1) → p5) ∧ (p4 ∨ (p5 → ((p5 ∧ (False → (p1 ∨ p1))) ∧ ((p4 ∧ p3) ∨ (p4 → p1)))))) ∧ p1) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_190107887800805980512939468568 : ((((p2 → (p4 ∨ (p1 ∧ p2))) → (True ∨ p4)) ∧ p2) ∨ ((((p5 → False) ∨ p2) → ((p1 → p5) ∧ (p2 ∨ p2))) ∨ ((False ∨ p3) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117270548985459699734961846950 : ((False ∧ ((False ∨ ((((False ∧ (p2 ∧ ((p4 ∧ p1) → (True ∧ False)))) ∧ p5) ∨ (p1 ∧ p1)) ∧ ((True ∧ p3) ∨ p5))) ∧ p3)) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264009999416400998221800915020 : (True ∧ ((((p3 ∧ p2) ∨ (True → (True ∧ False))) ∧ ((False → True) ∨ False)) → ((p2 ∧ ((p2 ∨ ((p3 ∧ p2) → p5)) ∨ (p4 ∨ True))) → p3))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
      -- Conjunctions on the left can always be decomposed.
      let h7 := h1.left
      let h8 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h12 =>
          -- One of the premise coincides with the conclusion.
          exact h10
        case inr h13 =>
          -- False on the left can always be used.
          apply False.elim h13
      case inr h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h15 =>
          -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
          have h16 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h14, we can now drive its conclusion.
          let h17 := h14 h16
          -- We need to get the right conjuct of h17 based on <expert-advice>.
          let h18 := h17.right
          -- False on the left can always be used.
          apply False.elim h18
        case inr h19 =>
          -- False on the left can always be used.
          apply False.elim h19
    case inr h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h1.left
      let h22 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h23 =>
        -- Conjunctions on the left can always be decomposed.
        let h24 := h23.left
        let h25 := h23.right
        -- Disjunctions on the left can always be decomposed.
        cases h22
        case inl h26 =>
          -- One of the premise coincides with the conclusion.
          exact h24
        case inr h27 =>
          -- False on the left can always be used.
          apply False.elim h27
      case inr h28 =>
        -- Disjunctions on the left can always be decomposed.
        cases h22
        case inl h29 =>
          -- We want to use the implication h28 based on <expert-advice>. So we show its premise.
          have h30 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h28, we can now drive its conclusion.
          let h31 := h28 h30
          -- We need to get the right conjuct of h31 based on <expert-advice>.
          let h32 := h31.right
          -- False on the left can always be used.
          apply False.elim h32
        case inr h33 =>
          -- False on the left can always be used.
          apply False.elim h33
  case inr h34 =>
    -- Disjunctions on the left can always be decomposed.
    cases h34
    case inl h35 =>
      -- Conjunctions on the left can always be decomposed.
      let h36 := h1.left
      let h37 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h36
      case inl h38 =>
        -- Conjunctions on the left can always be decomposed.
        let h39 := h38.left
        let h40 := h38.right
        -- Disjunctions on the left can always be decomposed.
        cases h37
        case inl h41 =>
          -- One of the premise coincides with the conclusion.
          exact h39
        case inr h42 =>
          -- False on the left can always be used.
          apply False.elim h42
      case inr h43 =>
        -- Disjunctions on the left can always be decomposed.
        cases h37
        case inl h44 =>
          -- We want to use the implication h43 based on <expert-advice>. So we show its premise.
          have h45 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h43, we can now drive its conclusion.
          let h46 := h43 h45
          -- We need to get the right conjuct of h46 based on <expert-advice>.
          let h47 := h46.right
          -- False on the left can always be used.
          apply False.elim h47
        case inr h48 =>
          -- False on the left can always be used.
          apply False.elim h48
    case inr h49 =>
      -- Conjunctions on the left can always be decomposed.
      let h50 := h1.left
      let h51 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h50
      case inl h52 =>
        -- Conjunctions on the left can always be decomposed.
        let h53 := h52.left
        let h54 := h52.right
        -- Disjunctions on the left can always be decomposed.
        cases h51
        case inl h55 =>
          -- One of the premise coincides with the conclusion.
          exact h53
        case inr h56 =>
          -- False on the left can always be used.
          apply False.elim h56
      case inr h57 =>
        -- Disjunctions on the left can always be decomposed.
        cases h51
        case inl h58 =>
          -- We want to use the implication h57 based on <expert-advice>. So we show its premise.
          have h59 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h57, we can now drive its conclusion.
          let h60 := h57 h59
          -- We need to get the right conjuct of h60 based on <expert-advice>.
          let h61 := h60.right
          -- False on the left can always be used.
          apply False.elim h61
        case inr h62 =>
          -- False on the left can always be used.
          apply False.elim h62



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180158347267402024115941765223 : ((((((p5 ∨ ((False ∧ p3) ∨ True)) ∧ p3) ∧ p5) → (p4 ∧ p4)) → True) → (((((p5 ∧ (p1 → False)) → p2) ∨ True) ∨ (p5 → p1)) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_111634242863022629377796205727 : (((((((True ∨ True) → (True ∨ True)) ∧ (((False ∨ p2) → False) → False)) ∧ ((False ∨ p1) ∨ (p3 ∧ (True → p3)))) ∨ p2) ∨ True) ∨ (False ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46901407814573032148811506878 : ((((((p3 → (False → ((((True → p2) ∨ ((p1 → p4) → p1)) → False) ∨ (p2 ∨ True)))) → False) ∨ (p4 → p2)) ∨ p5) ∨ (p4 → p4)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_673252631714133441782974066268 : ((((((p5 ∨ True) ∨ ((p1 ∨ p5) ∨ (p5 ∧ False))) ∧ ((p4 ∧ (p2 → (p2 ∨ (p5 → p4)))) ∧ (p2 → False))) → ((p5 ∨ True) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_664768051168861536416978922723 : ((((p1 → (((p4 ∨ p4) ∨ (p2 ∧ (((True ∧ (True ∧ p3)) ∧ ((p1 → (False ∧ p4)) ∧ (p3 ∨ p3))) ∨ p3))) → p5)) → (True ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_86563886516413335536400441421 : (((((True → p5) ∧ (p3 ∨ (p1 ∨ True))) ∨ False) ∧ (((p2 → p1) → False) ∧ (True → ((True ∨ (False → (p3 → (p5 ∨ p5)))) → p4)))) → p5) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h3.left
      let h9 := h3.right
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h10 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h11 := h5 h10
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h3.left
        let h15 := h3.right
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h16 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h17 := h5 h16
        -- One of the premise coincides with the conclusion.
        exact h17
      case inr h18 =>
        -- Conjunctions on the left can always be decomposed.
        let h19 := h3.left
        let h20 := h3.right
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h21 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h22 := h5 h21
        -- One of the premise coincides with the conclusion.
        exact h22
  case inr h23 =>
    -- False on the left can always be used.
    apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121567183984226138033388338144 : ((((True ∧ (p1 ∨ ((((False ∨ (True → p4)) ∧ True) ∨ (p5 → True)) ∨ (((p5 → False) ∧ False) → p3)))) → (p1 ∨ p3)) → p2) → (p3 → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157074728356720237866161538039 : (((p1 ∨ (True → (((((p1 ∨ (p3 ∧ ((p5 ∨ p1) → p4))) ∨ False) ∧ p5) → p2) → p1))) ∨ p5) ∨ (((p5 → (False → False)) ∨ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57147758904313074914127330014 : ((((p4 → p5) ∧ p4) ∨ ((True ∧ ((False ∧ (p1 ∨ ((p2 ∧ (False ∧ (p5 ∨ (True ∧ p1)))) ∧ p5))) → False)) → ((p3 → p5) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49748546664339260484396588028 : (((p5 ∧ ((((False → p5) → (p1 ∧ False)) ∧ (p5 ∨ (((p4 ∨ True) ∨ (p5 ∨ p2)) → (p2 → p4)))) ∧ p1)) → (p2 ∨ (p1 ∧ False))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h9 : (False → p5) := by
      -- Implications on the right can always be decomposed.
      intro h10
      -- False on the left can always be used.
      apply False.elim h10
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h11 := h6 h9
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h14 : (False → p5) := by
      -- Implications on the right can always be decomposed.
      intro h15
      -- False on the left can always be used.
      apply False.elim h15
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h16 := h6 h14
    -- We need to get the right conjuct of h16 based on <expert-advice>.
    let h17 := h16.right
    -- False on the left can always be used.
    apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657523463723739255865870128502 : (((((p5 ∨ p4) ∨ (p3 → (p5 ∨ (p5 → ((p5 → True) ∧ ((((p4 ∨ (p1 ∧ p2)) ∨ p4) ∧ (p5 → p1)) → p2)))))) ∨ (p1 ∨ True)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_69350337547551212988339279510 : ((p5 → (p2 ∨ (p3 ∨ (p4 ∨ ((p3 ∨ ((((((((p2 ∧ (p2 ∨ p5)) → p2) ∧ False) ∨ True) ∧ p4) ∨ p5) ∧ p1) → p3)) ∨ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256477279895703226617337289627 : ((False ∨ p4) → (((p2 → (p4 → (p1 ∨ True))) ∧ (p5 ∧ (p1 ∧ (p2 ∨ (p2 ∧ p4))))) ∨ ((((False ∧ (p2 ∧ p2)) ∧ False) → False) ∧ p4))) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- False on the left can always be used.
    apply False.elim h7
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671787824325670235799790188203 : ((((((p1 ∧ (p2 → (p5 ∨ p4))) ∨ ((p3 → p1) ∧ ((((p4 ∨ p2) ∧ (p2 ∨ False)) ∧ p1) ∧ p3))) ∧ p4) → ((p4 → False) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611840503488100919169643220575 : (((((p3 → ((True ∨ (p1 → p1)) → ((p3 ∨ p4) ∨ ((p1 → ((True ∧ ((p2 → p1) → False)) ∧ (p4 → p2))) ∨ p5)))) → p3) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788465553760277765889228932248 : (((p5 ∨ (((False → True) ∧ (True ∧ ((((((p1 → (((p4 ∨ p2) ∧ (p3 → p2)) ∧ False)) → p1) ∨ p2) ∧ p5) ∨ p1) → False))) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50787459357998179230697793908 : (((p5 ∨ ((((p3 → p5) → True) ∨ (p4 ∧ (False → ((False → (False → (p2 ∨ p1))) ∧ p5)))) ∧ p4)) → ((True → p2) → (p2 ∨ p1))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h10 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h11 := h2 h10
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h15 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h16 := h2 h15
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69214061461498630081558160203 : ((p5 → (((False → (True ∨ (True ∨ False))) ∨ False) ∧ ((p3 → (p4 ∧ ((True → ((False ∨ p3) → True)) ∧ p1))) → (p4 ∨ (p4 ∨ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_673982368407467782178063528050 : ((((True ∧ (p4 → (p5 ∨ ((((p2 → p4) → p4) ∨ (((p2 ∧ (p1 → False)) → (p1 ∧ False)) ∨ p4)) ∨ p2)))) → (p1 → (p2 ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114924681750227662975523987577 : ((((((p3 ∨ p2) → (p4 ∨ p4)) → ((p5 ∧ p5) ∨ p3)) ∧ (False ∨ p1)) → ((p3 → p4) ∨ (((True ∨ True) ∨ False) ∨ p1))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47251642649796658322093652995 : ((((((p5 ∨ p1) → (False ∨ p4)) ∨ False) ∨ (((True ∨ p5) ∨ p3) ∨ (True ∨ (((False → p5) ∧ p1) ∨ (p1 ∧ p5))))) ∨ (p4 ∧ p5)) ∨ p4) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175422051592043476321077271945 : ((False → (p1 ∨ (True → ((((p1 ∨ p5) ∨ p2) ∨ ((p1 ∨ True) → True)) ∧ True)))) → (((True → ((p4 → p3) ∧ p4)) ∨ (True ∨ p1)) ∨ p5)) := by
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
theorem thm_5_vars_177997735330559771928898251666 : (((False ∨ (p4 ∨ ((p2 ∨ (p5 ∧ (p5 ∧ (p2 → p2)))) ∨ True))) ∨ p3) ∨ (True ∧ ((((p1 ∧ (True ∧ (p1 → True))) ∨ True) ∧ p2) → p3))) := by
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
theorem thm_5_vars_234309403714536909053221654196 : ((p1 → (False ∧ p4)) → (((((p3 → p5) ∨ ((p1 → False) ∧ (False ∧ p2))) ∨ p3) → (p5 → p5)) ∧ (True → (False → (False ∨ (p5 ∨ True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- False on the left can always be used.
      apply False.elim h9
  case inr h11 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Implications on the right can always be decomposed.
  intro h12
  -- Implications on the right can always be decomposed.
  intro h13
  -- False on the left can always be used.
  apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748500858827140704375338839899 : ((((p3 → True) → ((((p5 → (p3 ∧ ((False ∨ (((p2 → p4) ∧ (p4 → (p1 ∨ False))) ∨ (p4 ∨ True))) ∧ p5))) ∧ p1) ∨ True) ∨ p1)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218963410266798532579590869718 : ((p4 ∧ ((p4 → p4) ∧ p3)) → ((False ∨ ((((p4 ∧ (False → (p2 ∨ False))) → (True ∧ ((p4 ∨ p1) ∨ p4))) → (False ∨ p2)) ∨ True)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_950764515703346139729053717646 : ((((p3 ∧ (p1 → p5)) ∧ (p3 → ((((p1 → (p1 ∨ (((False ∨ (p3 ∨ p4)) ∧ (True ∨ (False ∨ p1))) ∨ True))) ∧ p2) ∨ p3) ∧ p5))) → p5) ∧ True) := by
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
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h6 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46942857137412296088720743181 : ((((p2 ∨ ((p4 → (((True ∧ ((p5 ∧ (p3 ∧ ((p1 ∧ p2) ∨ False))) ∧ True)) → p2) → (p3 ∨ p3))) ∨ True)) ∨ p4) ∨ (True → p4)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48868154141291285666174013201 : (((p5 ∨ ((p1 → (p4 → (p3 → ((False ∨ (p2 → (True ∨ (p5 ∧ p1)))) → (p5 ∧ False))))) ∨ (p2 ∨ p4))) ∧ (p5 → (p4 ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_163786005302624262012055356099 : ((True ∧ (p1 ∨ (((p5 ∧ (p2 → p4)) → (((True → p5) ∨ p2) → (p4 → p4))) ∨ p5))) ∧ (p5 ∨ ((p5 ∧ True) → ((p2 ∨ True) ∨ False)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h1.left
    let h6 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h1.left
    let h9 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h10
  -- Conjunctions on the left can always be decomposed.
  let h11 := h10.left
  let h12 := h10.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178588425018833079137573949536 : ((((p4 ∧ (False ∧ (p5 ∨ p5))) ∨ p3) ∨ ((p5 ∧ p2) ∧ (True → p4))) ∨ ((((False ∨ p1) ∨ (False ∨ False)) ∧ p1) ∨ ((p5 ∧ p3) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306269390468634221745224585074 : (p1 ∨ ((p4 → (True ∧ False)) → ((p4 ∧ p4) → (False ∨ ((p4 ∧ (((True ∧ p5) ∨ (p4 ∧ ((p1 ∧ (p5 → p5)) → p3))) ∧ True)) ∧ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39562114840098192753049551591 : (((p1 ∨ (((p4 ∧ p5) → (((((p5 ∨ False) ∨ p2) ∧ ((p3 ∧ p5) ∨ False)) ∨ (p1 ∨ (True ∧ p3))) ∨ p2)) ∨ (p5 → True))) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48949480814207019626787824226 : ((((p3 ∧ (((p5 ∧ ((p1 ∧ (p1 → (p2 → p5))) ∨ p3)) → (p5 → (False ∧ (p4 ∧ p2)))) ∨ p2)) ∧ False) ∨ ((p3 → False) → True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_761744040101700992832716810681 : (((p3 ∧ ((p3 ∨ (p5 ∨ ((((p1 → ((True → p4) ∧ p5)) → (((p5 ∨ (False → p1)) → p3) → p5)) → (p1 ∧ p2)) → p4))) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112868633368030931917235513871 : (((((p1 ∧ p1) ∨ p1) → ((((p3 ∨ False) → (p5 ∨ (p3 → (p2 ∨ (False ∨ (False → (True ∧ False))))))) ∨ True) ∨ p1)) → p1) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_793866421179928602121861731199 : (((True → (p3 → (((p3 ∨ False) ∨ True) → ((((((p2 → p3) → p4) ∧ True) ∧ p4) ∧ (False ∨ p3)) ∨ (p2 ∨ (False → (True ∧ False))))))) ∨ p4) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- False on the left can always be used.
    apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322716929283333621380886814960 : (p5 ∨ ((((p1 → (((True → (p2 ∨ (p1 ∧ True))) ∧ p2) ∧ (p5 ∨ ((p5 → True) ∨ p3)))) ∨ (p3 ∨ (p1 ∨ (False → p4)))) → p1) → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p1 → (((True → (p2 ∨ (p1 ∧ True))) ∧ p2) ∧ (p5 ∨ ((p5 → True) ∨ p3)))) ∨ (p3 ∨ (p1 ∨ (False → p4)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168446642660766864102890078219 : (((True → False) → ((p1 ∧ (p4 ∨ ((p3 ∧ (p4 ∨ p3)) ∨ ((p1 → p5) ∧ False)))) ∨ True)) → (p2 → ((((True ∨ p1) ∨ True) → p3) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165126511800317822749426174081 : (((((p4 ∨ p1) ∨ ((p4 ∧ p1) ∨ (False → ((p2 → True) ∧ False)))) ∧ p2) ∧ (p2 → p3)) ∨ (False → ((p4 ∧ ((p3 ∨ p5) ∧ p3)) ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783301183361027145746874692750 : (((p3 ∨ ((p4 ∧ (((False ∧ (p5 ∨ (p5 ∧ True))) ∧ (True ∨ p4)) ∧ (p1 → ((False → p4) → p4)))) ∨ (((True ∨ p4) → p2) → True))) ∨ p3) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117528323934635900715436354363 : ((p2 ∧ ((p4 ∧ ((p2 → ((p5 ∧ ((p3 ∧ ((True → p5) → p4)) ∨ (p5 → p4))) → False)) → ((p3 → p1) ∨ p4))) → p3)) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338942450327541598783671132968 : (p1 → ((p4 ∨ p5) → ((False ∧ ((((((True → p5) → (p5 ∧ p2)) ∨ p1) ∨ (p3 → False)) → False) ∧ (True → ((p3 ∨ p2) ∧ True)))) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206464520635174346738752670118 : ((p4 ∨ (p1 ∨ ((p2 ∨ p3) ∨ p4))) ∨ (True → (((p4 → ((p1 ∨ (p1 → False)) ∧ ((p4 ∨ (p3 ∧ p2)) ∨ False))) ∨ True) ∧ (True → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164854586565248206943878462431 : (((False ∨ (((p4 ∧ (False → ((p1 → True) → (True ∨ False)))) ∨ p5) ∧ (p5 → p4))) ∨ p4) ∨ (((False ∧ (p4 ∨ p5)) ∧ (p3 ∨ p2)) → p5)) := by
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
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55894858453233337265012882212 : (((p2 ∨ (p4 → (p3 ∧ p3))) ∧ ((p3 → (((p1 → p1) ∨ p2) ∨ (((((p4 → p3) ∧ p4) ∧ p4) ∨ p3) ∧ (p5 → p2)))) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200673171107214373770024827245 : ((p1 ∧ (True ∨ (True ∨ ((False → p2) → p1)))) → (p1 → (((False → p4) ∧ ((p1 ∧ False) ∨ p5)) ∨ ((p2 → p1) ∨ (p1 → (False → p2)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
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
      -- Implications on the right can always be decomposed.
      intro h14
      -- False on the left can always be used.
      apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165677106673028956258766045348 : ((((((p1 ∧ p2) ∨ p1) → True) ∨ True) → (((p4 → (p2 ∧ False)) ∨ p2) ∨ (p5 → p4))) ∨ ((((p3 ∨ True) ∨ p4) ∧ (p1 ∧ p3)) → p3)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h3.left
      let h7 := h3.right
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h3.left
      let h10 := h3.right
      -- One of the premise coincides with the conclusion.
      exact h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h3.left
    let h13 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37298413109693923696982175486 : ((((True → (True ∧ (p5 ∧ ((p3 ∧ ((((p2 ∧ (p1 ∨ p2)) → p2) → (p5 → p1)) ∧ (True ∧ (True ∧ p3)))) ∧ p2)))) ∧ p3) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2099079450619017976861349290 : ((p2 ∨ ((True ∨ p4) ∧ (p4 ∨ ((((True → p4) ∨ (p5 ∧ (p1 ∧ p5))) ∨ True) ∨ p4)))) ∨ (((p3 ∧ (p3 → True)) → p2) ∧ True)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179317708316682811855218954918 : ((False ∨ (p4 ∨ ((False ∧ p5) ∨ (p4 → (False ∧ (False ∨ (p2 → p2))))))) ∨ (((p3 ∧ (((p1 ∧ p1) → p4) ∨ p1)) ∨ p3) → (True → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205998929941493346870298070803 : ((p1 ∧ (p3 ∨ ((False ∨ p3) ∧ p3))) ∨ ((p2 → (((p2 ∧ p3) ∧ (False ∨ ((((False → p4) → p3) ∧ (p1 → p2)) ∧ True))) → p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246731576187692690606765950024 : ((p5 ∧ p4) ∨ (p5 → (((False ∧ ((((True → p3) ∨ (p4 ∧ p3)) ∧ p3) ∧ (True ∨ ((p1 ∨ p3) → p1)))) ∨ (p3 ∨ p2)) ∨ (p1 ∨ p5)))) := by
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
theorem thm_5_vars_187257174101137874117197125750 : ((True ∧ (True ∨ ((p4 ∨ (p1 → p5)) ∨ (False → (p5 ∧ p1))))) → (((p3 ∨ p4) ∧ (p1 ∧ p5)) ∨ (((p1 ∨ p1) ∨ p4) → (True ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h10 =>
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
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h14 =>
          -- Disjunctions on the left can always be decomposed.
          cases h14
          case inl h15 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h16 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h17 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h19
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h20 =>
          -- Disjunctions on the left can always be decomposed.
          cases h20
          case inl h21 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h22 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h23 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h24 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h25
      -- Disjunctions on the left can always be decomposed.
      cases h25
      case inl h26 =>
        -- Disjunctions on the left can always be decomposed.
        cases h26
        case inl h27 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h28 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h29 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179492888237575262648948823126 : ((True → (p3 ∨ (False ∨ (p3 ∨ (True ∧ (p3 ∧ ((p3 ∧ False) ∨ False))))))) ∨ (((p1 ∨ ((p3 → False) ∧ False)) → True) ∨ (p1 → (p5 ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116454925835922120714263941761 : (((True ∧ p2) ∧ (p3 ∧ (p1 ∧ (p2 → (p1 ∧ ((((p2 ∨ p2) ∨ ((p4 ∧ p3) ∨ p2)) ∧ (p5 ∨ (p5 → False))) → p5)))))) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_931106802342421330732037532321 : (((((False → p4) ∨ ((p4 ∨ (p5 ∨ (False ∨ p3))) ∧ p1)) → ((p2 ∧ p2) ∧ ((((p1 → ((p3 → False) → p2)) ∨ p3) ∧ p1) ∧ p1))) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False → p4) ∨ ((p4 ∨ (p5 ∨ (False ∨ p3))) ∧ p1)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326356439551714898655266971375 : (p5 ∨ (p5 → ((((p5 → ((p5 ∧ False) → ((False → p1) → p2))) ∧ (False ∨ True)) → (False ∨ ((True ∧ False) ∧ False))) ∨ (p4 → (False → p5))))) := by
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
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_760390702885778904533131185249 : (((p2 ∧ ((p3 → p2) → ((p3 → (p5 ∧ p2)) ∨ (p3 ∨ (False ∨ (p2 ∨ ((p2 ∨ ((p1 ∧ (p5 → p3)) → True)) → (p2 ∨ p3)))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55258188993197381575560223558 : ((((p5 ∨ False) ∨ ((p1 ∧ p3) ∨ p2)) ∨ (((True → p4) ∧ (p4 ∨ ((True → p3) ∧ (True ∨ (((False → p4) → p5) ∨ p4))))) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56070232941586589842992509781 : ((((p2 ∧ (p5 ∨ p5)) → False) ∨ (((p1 → (p4 ∨ (p1 ∧ True))) → (p2 ∨ ((p2 → p2) ∧ ((p3 ∨ p5) ∨ (p1 → False))))) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111779065976846835970512097605 : ((((((False → (p2 ∧ p2)) → (p2 → (p2 ∧ (((p2 → (p4 ∧ p5)) ∧ p5) ∨ (p1 → p2))))) ∨ p3) ∨ (p5 → p2)) ∨ p3) ∨ (p4 → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115026226830144060034245830869 : (((p5 ∨ ((((p5 ∨ False) → p2) → (p4 ∨ (p2 → p1))) ∨ False)) ∧ (p3 ∨ (True ∧ (((p5 ∧ (False ∨ p1)) ∨ False) → p5)))) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311072560494591418662219405627 : (p2 ∨ ((p2 ∨ p2) ∨ ((True → ((((True ∧ (p4 ∧ False)) → p5) → p2) ∨ (((((p1 ∧ p4) ∧ False) ∧ p1) ∨ p4) → True))) ∨ (p5 ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299343193365769779940277504528 : (False ∨ ((((p3 ∨ p4) ∧ True) ∨ (((p1 ∧ (((p2 ∧ p5) ∨ ((False → (p3 ∨ (p1 → True))) → p4)) ∨ p2)) ∧ p2) ∨ (True → p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328780911087539909826360889463 : (True → (((((False ∧ (p5 → p5)) ∨ p5) ∨ (True ∧ p3)) ∧ p5) ∨ (((p2 ∨ (p4 ∨ True)) ∧ True) ∨ (False ∨ (((p4 ∨ p1) → p5) ∧ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_138146552475006647434914835896 : ((p1 → ((((p3 ∨ (p5 → ((False → p3) → (False ∨ ((True → p3) ∨ (p5 ∧ p2)))))) → (p2 ∨ p1)) → p3) ∨ p1)) ∨ ((True → True) ∧ True)) := by
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
theorem thm_5_vars_46047450293453625882856188324 : ((((p3 → ((((p4 ∧ ((p4 ∧ (p4 → (p2 ∧ p3))) ∨ p3)) → ((p2 ∧ p5) ∧ p4)) ∨ (p5 → p1)) → False)) ∧ False) ∧ (True → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_810279876235911265616939643234 : (((p5 → ((p5 ∧ ((((p3 → p1) ∨ p1) → (p5 ∧ p2)) → (True → p1))) ∧ ((p3 ∨ (p1 → (p4 ∧ (p4 → (p5 ∧ True))))) ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113429610569805188935557262856 : ((((((p4 → ((p5 ∧ True) ∨ (p4 ∧ (((False ∧ (False ∨ p1)) ∧ True) → True)))) ∨ (p1 ∨ p4)) ∧ p3) ∨ p4) ∨ (p2 → p1)) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347328669443921955327234608034 : (p3 → ((p5 ∨ (False → (((p1 ∧ p5) ∨ (p1 ∧ True)) ∧ False))) → (p4 ∨ ((True → True) ∧ (((p1 ∨ p5) ∧ (p3 ∨ p1)) ∨ (p2 ∨ p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135864488858459372580396440549 : (((((p3 ∨ False) ∧ (p5 → (p4 ∨ (p5 → p3)))) ∧ (p5 ∧ p2)) ∨ (((p1 ∨ p2) ∨ (True → (True ∨ p5))) ∨ True)) ∨ ((p1 ∧ p4) → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139782483175080056754779094874 : (((False ∨ (p1 ∨ (((((p3 ∨ (p5 ∧ p3)) ∧ p4) → p3) ∨ (((False ∨ p3) ∧ (True → p2)) → p4)) ∨ p1))) → False) → (p5 ∧ (True ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False ∨ (p1 ∨ (((((p3 ∨ (p5 ∧ p3)) ∧ p4) → p3) ∨ (((False ∨ p3) ∧ (True → p2)) → p4)) ∨ p1))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- One of the premise coincides with the conclusion.
      exact h9
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h2
  -- False on the left can always be used.
  apply False.elim h10
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h11 : (False ∨ (p1 ∨ (((((p3 ∨ (p5 ∧ p3)) ∧ p4) → p3) ∨ (((False ∨ p3) ∧ (True → p2)) → p4)) ∨ p1))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h12
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h15 =>
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- One of the premise coincides with the conclusion.
      exact h18
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h19 := h1 h11
  -- False on the left can always be used.
  apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301967948552978171665326349790 : (False ∨ ((True → p3) → ((((p5 ∧ p5) ∧ ((p4 ∧ (True ∨ ((p2 ∧ False) → False))) ∨ p3)) ∨ p4) → ((((p5 ∧ p1) ∧ p2) ∨ p4) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h14 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246635924146345915721633873231 : ((p5 ∧ p3) ∨ (((((p5 ∧ True) ∧ p3) → p5) → (((True → p3) ∨ False) ∨ (p1 ∧ ((p1 ∧ False) ∨ False)))) ∨ ((p2 ∨ p3) → (False → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245130364442737746367347208872 : ((p2 ∧ True) ∨ ((p5 ∧ (p2 ∨ p1)) ∨ ((((False → p4) ∨ True) → (False → (True → True))) → (((True → (p5 ∧ False)) → p4) ∧ (False ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- False on the left can always be used.
  apply False.elim h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_639634377934612474637236838440 : (((((p2 ∧ (p2 → p5)) ∧ (p2 ∨ (False → (p1 ∨ (p5 → ((p1 → (((p2 → True) → ((True ∨ False) ∧ p4)) ∨ p5)) → p4)))))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43419535849935011530669227504 : ((((((p2 ∧ (False ∨ False)) ∨ ((False ∨ True) → p4)) → ((p4 → (((p2 → (p5 → p2)) ∧ (p4 → p5)) ∨ p4)) → p4)) ∨ p3) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657511049393095383268923948220 : (((((p4 ∨ False) ∨ (((((p1 ∨ p5) ∧ p4) ∧ ((p5 ∨ (True ∧ (p5 → True))) → ((p3 ∨ True) ∧ False))) ∨ p2) ∧ True)) ∨ (p5 → p5)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160958994968253015415277492481 : ((((p3 ∨ p2) → p4) ∧ (p1 → (((p2 ∨ ((p5 ∧ p4) ∨ p2)) ∨ ((True ∧ p2) → p5)) ∨ True))) → ((p5 → ((p4 → True) → p3)) ∨ True)) := by
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
theorem thm_5_vars_133702702107420307616619765032 : (((((p1 → ((p4 ∧ p4) ∧ True)) → (((p4 ∨ p2) ∧ p5) ∧ (p5 → p1))) ∧ ((p4 → p5) ∨ (p4 ∧ p2))) ∧ False) ∨ (p4 ∨ (True ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180418971582325251728143337044 : ((((p2 → ((p2 ∨ ((False → p4) ∧ True)) ∨ p1)) ∧ p5) → (p1 ∧ p1)) → (((((False ∨ p1) → False) → True) → (p1 ∧ (p2 ∧ p5))) → p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (((False ∨ p1) → False) → True) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- One of the premise coincides with the conclusion.
  exact h7



