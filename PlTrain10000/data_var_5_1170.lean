variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150008636802103505752879686761 : ((p5 ∨ (((((False → p2) → ((p1 ∧ (p2 ∧ p2)) → (((p1 → p3) ∨ p3) ∧ p4))) ∨ False) → p4) → p3)) ∨ ((False → p1) ∨ (p5 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173977841949895247981641957236 : ((((p3 → (False ∧ True)) ∨ (False → (p3 → ((p1 ∨ (p4 ∧ True)) ∧ True)))) → False) → (((True → (p5 ∨ (True ∧ p4))) ∨ (p1 ∧ p1)) ∧ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p3 → (False ∧ True)) ∨ (False → (p3 → ((p1 ∨ (p4 ∧ True)) ∧ True)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- False on the left can always be used.
  apply False.elim h5
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : ((p3 → (False ∧ True)) ∨ (False → (p3 → ((p1 ∨ (p4 ∧ True)) ∧ True)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h7
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h6
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_816410144951726916734051885417 : ((((((((True ∧ p5) ∧ p2) ∧ ((((((False → p5) ∧ p5) → p2) → p5) ∨ True) → (p3 ∧ False))) ∨ (p2 ∨ (p3 → p3))) → False) ∧ p4) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((((True ∧ p5) ∧ p2) ∧ ((((((False → p5) ∧ p5) → p2) → p5) ∨ True) → (p3 ∧ False))) ∨ (p2 ∨ (p3 → p3))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152698791846489922303995441281 : (((p4 ∧ True) ∨ (((p4 ∨ True) ∨ ((p3 ∨ p3) ∧ (p3 → (True → p1)))) ∧ (((False ∧ p3) ∨ p2) ∧ p1))) → (((p5 ∨ p3) ∨ p2) ∨ p4)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h7.left
        let h11 := h7.right
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h12 =>
          -- Conjunctions on the left can always be decomposed.
          let h13 := h12.left
          let h14 := h12.right
          -- False on the left can always be used.
          apply False.elim h13
        case inr h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h9
      case inr h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h7.left
        let h18 := h7.right
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h19 =>
          -- Conjunctions on the left can always be decomposed.
          let h20 := h19.left
          let h21 := h19.right
          -- False on the left can always be used.
          apply False.elim h20
        case inr h22 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h22
    case inr h23 =>
      -- Conjunctions on the left can always be decomposed.
      let h24 := h23.left
      let h25 := h23.right
      -- Disjunctions on the left can always be decomposed.
      cases h24
      case inl h26 =>
        -- Conjunctions on the left can always be decomposed.
        let h27 := h7.left
        let h28 := h7.right
        -- Disjunctions on the left can always be decomposed.
        cases h27
        case inl h29 =>
          -- Conjunctions on the left can always be decomposed.
          let h30 := h29.left
          let h31 := h29.right
          -- False on the left can always be used.
          apply False.elim h30
        case inr h32 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h32
      case inr h33 =>
        -- Conjunctions on the left can always be decomposed.
        let h34 := h7.left
        let h35 := h7.right
        -- Disjunctions on the left can always be decomposed.
        cases h34
        case inl h36 =>
          -- Conjunctions on the left can always be decomposed.
          let h37 := h36.left
          let h38 := h36.right
          -- False on the left can always be used.
          apply False.elim h37
        case inr h39 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h39



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_758901592511504838520694820544 : (((p2 ∧ ((((((False ∧ p1) → (((True ∧ p4) ∧ (p1 → (p1 ∨ False))) → (p2 → p4))) → True) → p5) ∧ ((False ∨ p4) ∨ p1)) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245497692829734339095737193300 : ((p2 ∧ p5) ∨ ((p1 ∧ p1) ∨ ((p1 ∧ False) ∨ (p2 → ((p3 ∨ p2) ∧ (True ∧ (False → (((p3 ∧ p5) ∧ (True ∧ True)) ∧ (False → False))))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133620443355779423689989315593 : (((((True ∨ ((True → p4) ∨ (p4 ∨ p5))) ∨ ((p4 ∨ ((p1 ∨ (p5 ∧ p5)) ∧ (p5 ∧ p2))) → p5)) → p1) ∧ True) ∨ (p4 → (False ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_714600041831294127003374575836 : (((((p4 ∨ p3) ∨ ((True → p1) → p3)) → (((((p5 → (p2 ∨ (p4 ∨ p4))) ∨ ((p1 → (p1 ∧ True)) ∨ p5)) → p1) ∧ p2) ∨ True)) ∨ False) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670157607629657660816604347627 : (((((((False ∧ p3) ∧ p3) → (p5 ∨ True)) → (p5 → (p4 → ((p5 → False) ∧ ((p5 ∨ (True → p3)) → True))))) ∨ (False → (p5 → p1))) ∨ p2) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122507276293573644066565333339 : (((p1 ∧ ((((((p5 ∨ True) → p4) → (((p1 → True) → p1) ∨ (p2 ∨ (p1 ∧ False)))) ∨ p4) → p3) → p2)) ∨ (True ∧ p4)) → (p4 → p4)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326344464735094563109362582628 : (p5 ∨ (p5 → ((p1 → (((False → True) ∧ ((False → p1) ∧ (p5 ∨ ((p1 → (p5 ∧ p1)) ∨ p2)))) → ((True ∧ True) ∧ (p2 ∧ True)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215133112952755922650116965000 : (((p4 → p1) → (p2 → p5)) ∨ ((p2 ∧ ((p1 ∧ (p1 ∨ p3)) ∨ ((((p3 → p4) ∨ (True → p2)) ∧ p3) ∧ ((p3 → p5) → p3)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50221809715377994849790736633 : (((((p1 → p4) → (((False ∧ (p3 → ((p2 ∨ True) → p5))) ∧ (True ∧ (p3 ∧ p5))) ∧ p1)) ∨ True) ∨ (p2 ∧ (p3 ∧ (False ∨ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_733386900344980953555657089182 : ((((p4 ∧ False) ∧ ((((((p3 ∨ p1) ∧ False) ∧ (p3 ∨ p5)) → ((((p4 ∨ p1) → False) → True) ∨ p4)) ∧ (p1 ∧ (p3 ∧ p1))) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_36300607963079907605554594324 : ((p4 → (((p4 → False) ∧ (p1 ∨ (((True ∨ ((((p1 → ((False → True) → (p1 ∨ p5))) ∧ p5) → p5) ∧ p4)) ∨ False) ∧ p2))) → p5)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h6 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h1
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
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h13 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h1
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h14 := h3 h13
        -- False on the left can always be used.
        apply False.elim h14
      case inr h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h15.left
        let h17 := h15.right
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h18 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h1
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h19 := h3 h18
        -- False on the left can always be used.
        apply False.elim h19
    case inr h20 =>
      -- False on the left can always be used.
      apply False.elim h20
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49098688157751101799605496555 : ((((((True ∧ (p4 ∨ ((True ∧ (p2 ∧ (False ∨ (p3 ∧ p4)))) ∧ p5))) → True) ∧ p5) → (p3 ∧ (False ∧ p1))) ∨ ((p3 → p5) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66008292965767785148343781919 : ((p5 ∨ ((((((p3 ∧ ((p1 ∨ p2) → p5)) ∨ p3) ∧ p2) → ((p4 ∧ p2) ∨ (False → ((p1 ∨ (p4 ∨ True)) → p1)))) ∧ p2) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49093685354622424222396941826 : ((((((((p3 ∨ (True ∨ True)) ∧ False) ∨ (p1 ∨ False)) ∧ (False ∧ p2)) ∨ (p5 ∨ p2)) ∨ (p1 → (p1 → p1))) ∨ ((p3 ∧ p4) ∧ p1)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_264402352923072630844904458120 : (True ∧ ((False ∧ ((False ∧ p3) ∨ False)) ∨ (((True ∨ False) ∧ p1) ∨ ((p2 → (True ∨ False)) ∨ (p3 → (False ∨ ((p3 → (False ∧ p2)) ∨ p1))))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254208361391130781370456110316 : ((p2 ∧ p2) → ((((p1 ∧ p3) ∧ (p3 ∧ (((p2 → ((False ∨ (((p1 ∨ (p2 ∧ p3)) → p5) → False)) ∧ p5)) ∨ True) ∨ False))) ∨ p3) ∨ p2)) := by
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
theorem thm_5_vars_60121282852224254935662526782 : (((p3 ∨ p5) → (((((((False → True) ∧ p4) ∨ p3) ∨ (p4 → p5)) → ((((p1 ∨ True) → p4) → False) → (p4 ∨ p3))) → p3) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698107201679534285871217792765 : (((((p4 ∨ (((p5 → ((p1 → p4) ∧ p5)) → p1) ∨ p4)) ∨ True) ∨ (p4 ∧ ((True ∧ p2) → (((p3 ∧ (p2 → False)) ∨ False) ∨ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190047729455190649823530706756 : ((((False ∧ ((p5 → (p3 → False)) → False)) ∨ p3) ∧ p1) ∨ ((p4 → (p4 ∧ (p4 → ((False → (p2 ∧ p1)) ∨ (p3 ∨ (p2 → p2)))))) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_107509083055365595316155373854 : (((p1 → (p4 → p5)) → ((((((p4 ∨ (p4 ∨ (p5 ∧ p3))) ∧ False) → p1) → p4) ∨ ((p1 ∧ (p1 ∧ True)) → p1)) ∨ p1)) ∧ (p1 ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119323411657185338649560231414 : ((p3 → ((p4 ∧ (((False ∧ (p3 ∧ p2)) → (p1 → p3)) ∧ ((p1 ∨ p1) ∧ p2))) → ((((p2 ∨ False) → False) ∨ p2) → False))) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780751794677313688029334752421 : (((p2 ∨ (((True → (p5 ∧ (True ∧ False))) ∧ p5) → (((p4 → (p3 ∧ p5)) ∨ (p1 ∧ ((False ∨ ((p1 ∧ p1) → p4)) ∨ p4))) ∧ p3))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h10 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h11 := h8 h10
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- We need to get the right conjuct of h12 based on <expert-advice>.
  let h13 := h12.right
  -- False on the left can always be used.
  apply False.elim h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123173692468400507340680145044 : (((p4 ∨ ((((((p2 ∨ True) ∧ (False → False)) ∨ p2) ∨ ((p2 ∧ (p1 → p3)) → True)) ∧ p1) ∧ True)) → (p2 → (p3 ∧ True))) → (p3 → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47248829670602014635630117171 : ((((p1 ∨ (False ∨ ((p2 ∨ False) ∧ True))) ∧ ((p2 ∧ ((p5 → True) ∨ ((p5 ∧ False) ∨ p4))) ∨ ((p2 ∨ True) ∨ p1))) ∨ (p1 ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67908714034136368093776976824 : ((p2 → (((False ∧ (p3 ∨ (p2 ∨ (True ∨ p5)))) ∨ (True ∧ ((p3 → p2) ∨ False))) → ((((p5 ∧ p3) → p5) ∧ (True ∧ p1)) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618150714068717225280230522302 : (((((p4 ∨ ((True ∧ p1) ∨ True)) ∧ (p1 ∨ ((((True ∧ ((True ∧ p4) ∨ p1)) → (p5 ∨ True)) → p3) ∨ (False ∨ (p5 → True))))) ∨ False) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200757072021025833270690016083 : ((p4 ∧ ((((p4 ∧ p5) ∨ p3) ∨ True) ∧ p5)) → (((((p3 ∧ False) ∧ p3) → ((p4 ∨ (True ∨ True)) ∨ (p2 ∧ p2))) → p2) ∨ (p4 ∨ p1))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355864328614708086908679074294 : (p5 → (((p1 → ((False ∧ (p4 ∨ p5)) ∨ p4)) ∨ ((False ∧ (p1 ∨ ((p2 ∨ (p4 ∧ (p3 → p3))) → p3))) ∨ False)) ∨ (p5 ∨ (False ∧ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116069721641466249712663219029 : ((((p4 ∨ p4) ∧ True) ∧ ((p3 ∧ (p1 → (((True → (p4 ∧ (p1 ∧ (p5 ∨ False)))) → p1) ∧ (True ∧ (p4 ∨ False))))) ∨ True)) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_495522784718045079132925955741 : ((((p1 → (p3 ∧ (p1 ∧ p4))) → ((p3 ∨ ((p3 ∧ ((p2 ∨ p2) → (False ∧ p4))) ∧ (False → (((p2 ∨ p4) → p3) ∧ p2)))) ∨ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177720730368715334180856865816 : ((((p2 → (((True ∨ True) → False) → p2)) → (p1 ∨ (p3 ∨ p2))) ∧ p4) ∨ ((((p4 ∨ ((False → p5) ∨ p1)) → False) → p1) ∨ (p2 ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p4 ∨ ((False → p5) ∨ p1)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51162704061407046396797642791 : ((((((p4 → ((p1 ∨ ((True → False) ∨ p1)) → p4)) → p5) ∨ (p1 ∧ p3)) ∧ (p2 ∧ False)) ∨ (p4 ∧ (p2 ∨ ((p1 ∨ False) ∨ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148220741444204884487810167103 : ((((False ∨ (((False → (p5 ∧ (p2 ∧ p5))) ∧ (p4 ∧ (p4 → p2))) ∧ p1)) ∧ p5) ∨ (p3 ∧ (p2 → p5))) ∨ (p3 → (p2 → (p2 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134488691355492232214307981058 : ((((((((p2 ∧ p5) ∨ (p3 ∨ False)) → ((True → (False ∨ ((True ∨ p1) → p2))) → p4)) → p4) → p5) ∨ False) → p4) ∨ (False → (p4 ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_10532818854009887272280780554 : (((p3 → (((((p3 ∨ (((p1 → p4) ∧ p1) ∧ p1)) → (p1 ∨ (p4 ∧ p3))) ∧ (p1 ∨ p3)) ∨ p4) ∨ (p1 ∨ (False ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58415693613571860372664722942 : (((p2 ∨ p2) ∧ (p4 ∨ (p2 ∨ (((p3 ∧ p3) ∨ ((True ∧ ((p2 ∨ ((False ∧ p2) → p3)) ∨ False)) ∧ False)) ∧ (p5 → (p4 ∨ p1)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317752926448359315756900142253 : (p4 ∨ ((((((p1 ∨ False) ∨ ((False ∧ (p4 → (p1 → (False → (p5 → True))))) ∨ p5)) ∧ True) → p5) → ((p5 ∧ (p4 → p5)) ∧ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116871451701459594306780521442 : (((p2 → p1) ∨ ((p4 ∧ ((p4 ∧ ((p1 ∧ True) → p1)) → ((p3 → p2) ∧ (False ∨ ((p1 ∨ p4) ∧ p5))))) ∨ (p4 → True))) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_761339999417034320328834599202 : (((p3 ∧ (((False ∧ (((p5 ∧ (False ∧ ((p5 ∨ False) → p3))) → (p2 ∨ (p4 → p4))) ∧ p4)) ∧ (((p1 → True) ∧ p5) ∧ p4)) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158329936414676979388657477357 : (((True ∧ p5) ∧ (((True → True) → p4) → ((p5 ∧ ((p3 ∧ p5) ∨ (p3 → (p5 ∧ p4)))) ∧ p4))) ∨ (p4 ∨ (p5 ∨ (False ∨ (False → p2))))) := by
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
theorem thm_5_vars_112065497227963351638881666941 : ((((p4 ∨ p4) ∧ (False ∧ (p4 ∨ ((p5 ∧ p4) ∨ ((((p3 → p5) ∧ (p5 ∧ p4)) ∧ ((p5 ∧ True) ∧ p4)) ∨ p3))))) ∨ p4) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185380645665484301525108527865 : ((p5 ∧ (((p4 ∨ p4) ∧ p2) ∧ (False ∧ ((False → False) ∨ p1)))) ∨ ((p4 ∧ (((p3 → p4) ∨ (p1 ∧ False)) → False)) → (False ∧ (True → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((p3 → p4) ∨ (p1 ∧ False)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- False on the left can always be used.
  apply False.elim h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h10 : ((p3 → p4) ∨ (p1 ∧ False)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h11
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h12 := h9 h10
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134347330747323811320694323525 : (((p5 ∧ (p5 ∧ ((p2 ∨ p1) → (p1 → (((p2 ∨ (False ∧ True)) → ((p2 → True) ∧ False)) ∧ (p1 → p2)))))) ∨ p3) ∨ ((True ∨ p3) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336199894855581231419304968370 : (p1 → ((((False ∨ (((((p5 ∧ p1) → p4) ∧ p5) ∨ p2) ∨ p1)) ∧ (((p2 ∨ p5) ∧ ((True → p4) → p2)) ∨ p2)) ∨ (False → p4)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_691702821404267968657468619121 : ((((False ∨ ((((p2 ∨ p4) ∨ p1) → (((p1 → p3) ∨ p2) ∧ (False ∧ True))) ∨ p1)) → ((p1 ∨ (p1 → True)) ∧ (p5 → (p2 ∨ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185932213405701642673186151143 : (((((p1 ∧ True) ∨ True) → (p2 → (p5 → (p4 ∧ False)))) ∧ p1) → ((((p1 → p1) → (p4 → (p2 → ((p4 ∨ False) → p3)))) ∧ p3) ∨ True)) := by
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
theorem thm_5_vars_264181918041936628444896100103 : (True ∧ ((p5 → (p1 → (((p1 ∨ p3) ∨ p3) ∧ p3))) ∨ (((p1 ∨ ((p5 ∧ p4) → p3)) ∨ (p1 → ((p3 ∨ (p4 ∨ p1)) ∧ p1))) ∨ p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356636350350473803094325912182 : (p5 → ((False ∨ ((((False ∧ p1) → p2) → True) → p2)) ∨ (((p3 ∧ ((p3 ∧ (((p5 → False) → p3) → p3)) → True)) → (p2 → p4)) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_701830768892403170520998991626 : ((((p4 ∧ (p5 ∧ (False ∨ (p2 ∨ (True → (False → p3)))))) ∧ ((((((p1 → p1) → (p4 ∧ p5)) ∧ p4) → p3) ∨ p3) ∨ (p3 ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4058855928955451290745898736 : (p2 ∨ ((True ∧ True) → ((p4 ∧ (p3 ∨ ((p3 → p2) → (True → p3)))) ∨ (((p5 ∨ ((p2 → True) ∨ p5)) → (p4 ∨ p5)) ∨ True)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59241730820336887184961791136 : (((p2 ∨ p2) ∨ (p4 ∧ ((((((p2 ∧ p2) ∨ p2) ∨ p1) ∨ p3) ∧ ((False → (p5 → p4)) → (True ∨ p2))) ∧ ((p2 ∨ p2) ∨ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149675720549899392263716172529 : ((p5 ∧ ((p4 ∨ (p5 → (((True ∧ ((p2 ∨ ((p2 ∨ p3) ∧ p1)) ∨ False)) ∨ p4) ∨ (p1 ∧ p5)))) ∧ p2)) ∨ (p5 ∨ ((p3 ∧ p3) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244422022694059318197227291612 : ((False ∧ p1) ∨ (p3 → (((((p2 ∧ (p2 → (p3 ∨ p5))) ∨ (p5 ∨ p4)) ∨ (True ∧ True)) ∨ ((p2 ∨ ((p1 → p1) ∨ p2)) ∨ True)) ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114010592018064175531690653908 : ((((p4 ∧ ((((True ∨ p1) ∧ ((p4 → p5) → p5)) ∨ p4) ∨ (p5 ∨ ((p5 → p2) ∧ True)))) ∧ False) ∨ (p3 ∧ (p1 ∧ p4))) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50301194335113491961547515546 : ((((((p2 ∨ p3) ∧ ((False ∧ (((p1 ∧ False) → p5) → p4)) ∧ p3)) → p2) → (p4 ∧ (True ∨ p4))) ∨ ((p3 ∧ (p3 ∧ p4)) → True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_641764882461159128275492571326 : (((((p4 ∨ False) → (False ∨ ((p3 → p4) ∨ ((p4 ∨ p3) → ((p4 ∨ ((False ∧ (True ∧ ((p1 ∨ True) → p1))) ∨ p1)) ∧ p3))))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247451788282482718126202533210 : ((False ∨ p2) ∨ (p1 ∨ ((p1 ∨ p1) ∨ ((((((p5 ∧ (False ∧ (p2 ∨ (False ∨ (p4 ∧ p3))))) ∨ True) → (p4 ∨ p1)) → p1) ∨ True) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_356047030740764911902089981133 : (p5 → ((p2 ∨ ((False ∧ ((((False ∨ ((p5 → p5) ∧ p5)) ∧ (False ∧ p4)) ∨ p3) ∧ (p5 ∨ False))) ∧ True)) ∨ ((p4 ∧ (p4 → p3)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51514622179395450554857888748 : ((((p5 ∨ p5) ∧ (((p3 ∧ ((False ∧ p2) ∧ p4)) → p5) ∧ ((p4 → (True ∨ p4)) → p2))) → (p1 → ((False → (True → p3)) ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53037685185879508873619329749 : (((((True ∨ False) ∨ p1) → (p3 ∨ ((p1 ∨ (p4 ∨ p3)) ∧ p5))) ∧ (p5 ∨ ((((p1 ∨ p1) ∨ (p2 ∨ False)) → (p3 ∧ True)) ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185437639774468649256175594326 : ((False ∨ ((((p2 ∧ p4) → False) ∧ (p4 ∨ p4)) → (False ∧ p2))) ∨ ((((False ∨ (((p3 ∨ True) ∧ p1) ∨ p2)) → (p5 ∧ False)) ∧ p1) → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_646926908283558191858218245344 : ((((p2 → (True → (p1 → (((((True → (p2 → (p4 → p1))) ∨ ((p3 → p4) ∨ True)) ∧ (p3 → False)) → False) ∨ (p5 → p3))))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699258179684111790083289239242 : ((((p5 → ((False ∧ True) ∨ (p4 ∧ ((False ∧ (False ∨ p5)) ∨ p3)))) ∨ (((True ∧ p1) ∧ (False ∧ True)) → ((p1 ∨ False) ∨ (p1 → p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612642389327117345147453769512 : (((((((False ∨ ((p1 ∧ p1) ∨ p2)) → ((p4 ∧ (True → (p3 → (p2 ∧ True)))) ∨ p1)) ∧ ((p1 ∨ p2) ∧ False)) ∨ (p4 → True)) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183981907912027771224498251023 : ((((((p4 ∨ False) → ((False ∨ p2) ∧ p1)) ∨ p5) ∧ False) ∨ p3) ∨ (False → ((p1 ∧ ((p1 ∨ p5) → ((True ∧ (False ∧ p3)) → p2))) ∧ p3))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- False on the left can always be used.
  apply False.elim h6
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_687904930693074688979553963704 : (((((p3 ∧ (False → ((p2 ∧ (p3 ∧ (p1 ∧ p2))) ∨ p2))) → ((p3 ∨ p1) → p5)) ∧ (p1 → (((True → p4) → p2) ∧ (False ∧ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705924556189809352245820222910 : (((((False → (p2 → False)) ∨ (p5 → (p2 ∧ False))) ∧ ((((p4 ∧ p3) → (False ∧ ((p3 → (True ∨ p2)) ∧ p2))) → (p3 ∨ p3)) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608012994674622870024983923401 : (((((p4 → (p4 ∧ (p3 ∨ (((False ∧ (True ∨ False)) ∨ (p5 ∧ p2)) ∧ ((False ∨ (p4 ∧ p4)) ∧ (p5 ∧ (True ∧ p2))))))) ∧ True) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_47531434037281230066166768429 : (((p4 ∨ ((((p5 ∨ (p3 ∨ (p2 ∨ p4))) ∨ (True → (p5 ∧ True))) ∧ (p2 ∧ (False ∧ p4))) ∨ (p5 → (p5 ∧ False)))) ∨ (p1 ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_673106663083156541341700065076 : ((((((p2 → True) ∨ ((p1 ∧ (p1 ∧ (True ∧ p4))) ∧ (True ∨ p5))) ∨ ((((p1 ∧ False) ∧ p2) ∨ True) → p3)) → ((p5 → True) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126486737086679569229895255324 : ((p2 ∧ (((p1 → (p4 → p4)) → (p2 → (p4 ∧ p3))) ∨ ((p2 ∧ ((p1 ∨ True) → (p2 ∨ (p2 → False)))) → (False ∧ False)))) → (p1 ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : (p1 → (p4 → p4)) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h8 := h4 h5
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h9 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h10 := h8 h9
    -- We need to get the left conjuct of h10 based on <expert-advice>.
    let h11 := h10.left
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h13 : (p2 ∧ ((p1 ∨ True) → (p2 ∨ (p2 → False)))) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h2
      -- Implications on the right can always be decomposed.
      intro h14
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h16 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h2
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h17 := h12 h13
    -- We need to get the left conjuct of h17 based on <expert-advice>.
    let h18 := h17.left
    -- False on the left can always be used.
    apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53170932389526157721792188769 : (((((((p5 ∨ (p4 ∧ (p3 ∨ p3))) ∧ p3) ∨ True) → p1) → False) ∨ (p5 ∨ (True → (((True ∧ (True ∨ (True ∨ False))) ∨ p3) ∨ p5)))) ∨ p3) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42034238262665319001607178005 : ((((p3 ∧ p4) ∨ (False ∧ (((False ∧ ((((((p1 → p3) ∨ (p1 ∧ False)) ∨ p2) ∨ (False ∧ p4)) ∧ p5) ∧ False)) → False) → p5))) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46196458268088588087452353571 : ((((p5 ∨ ((((False → (((p1 → p4) → p2) ∨ ((p4 → p1) ∨ p4))) ∧ (p4 → p2)) ∨ (False ∧ p2)) ∨ True)) → p5) ∧ (p3 ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312522380860379863204379010524 : (p2 ∨ (p5 → (p2 → (((True → ((p1 ∨ p2) ∨ p4)) ∧ p3) → (((p4 ∨ p2) → False) → (((False → p3) ∧ False) ∧ (p4 → (p3 → False)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h3.left
  let h7 := h3.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h8 : (p4 ∨ p2) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h9 := h4 h8
  -- False on the left can always be used.
  apply False.elim h9
  -- Implications on the right can always be decomposed.
  intro h10
  -- Implications on the right can always be decomposed.
  intro h11
  -- Conjunctions on the left can always be decomposed.
  let h12 := h3.left
  let h13 := h3.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h14 : (p4 ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h10
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h15 := h4 h14
  -- False on the left can always be used.
  apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_106576417843179947081456727536 : ((((False → (((p2 → False) → p1) ∧ p3)) → True) → (((p2 → False) ∨ ((p3 ∧ (p5 ∧ False)) ∨ True)) ∧ ((False ∧ p5) → False))) ∧ (p5 ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47754106619421658841996729657 : (((((True → p4) ∧ ((((p4 ∨ p5) → ((p4 ∧ p1) ∨ True)) ∨ (((False ∨ (p2 ∧ False)) ∨ p4) ∨ p5)) → p3)) ∨ p1) → (p5 ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42052436930803414146515507555 : ((((p1 ∨ p4) ∨ ((p3 → ((((False ∧ False) ∨ (p3 ∧ (((p2 ∨ p2) → p3) → p4))) → True) ∨ p4)) → (p3 → (p5 ∧ True)))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214452480060865591585669959708 : (((p5 → (p5 ∨ p3)) → p4) ∨ ((p5 ∨ (((p4 ∨ p3) → (((False ∨ p2) ∧ p4) → False)) ∧ ((p3 ∨ p4) ∨ (p2 ∧ (p4 ∨ p4))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193978435266595930564978191653 : ((p3 ∨ (((True ∨ p4) → (p2 ∨ True)) ∨ (p5 ∨ True))) → (((False ∨ p4) → (((p2 ∧ (((p1 ∧ p1) ∧ p1) ∨ p1)) ∧ p1) ∨ p5)) ∨ True)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246208385541953188412688030646 : ((p4 ∧ p3) ∨ ((((p3 → (p1 ∧ ((False ∧ (p1 → (p2 ∨ (p3 ∧ p1)))) ∧ p5))) ∧ False) ∨ ((p3 ∨ True) → p4)) ∨ (p5 → (False → True)))) := by
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
theorem thm_5_vars_816927270714964303366882137343 : ((((((False ∨ True) ∧ ((p1 ∨ (((((False ∨ False) ∧ p1) → ((p1 ∧ p2) ∧ p1)) ∨ (p2 ∨ p3)) → p5)) ∨ (p4 ∨ True))) → False) ∧ p3) → False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((False ∨ True) ∧ ((p1 ∨ (((((False ∨ False) ∧ p1) → ((p1 ∧ p2) ∧ p1)) ∨ (p2 ∨ p3)) → p5)) ∨ (p4 ∨ True))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56123215611870909920907099948 : ((((p4 ∨ p3) ∨ (p2 → p4)) ∨ ((((p3 → (True ∧ p1)) ∨ ((p3 ∨ (((p3 ∧ p4) ∨ True) ∨ (p3 ∧ p4))) ∨ p4)) → False) → False)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p3 → (True ∧ p1)) ∨ ((p3 ∨ (((p3 ∧ p4) ∨ True) ∨ (p3 ∧ p4))) ∨ p4)) := by
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707772060731151085981004311415 : ((((True ∧ ((p4 ∧ (False ∨ True)) ∨ (p4 ∨ p1))) ∨ (p2 ∨ (p4 → ((((True → p4) ∨ p2) ∨ ((True ∧ p5) ∨ p4)) ∨ (p3 → True))))) ∨ False) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201766651466464721677233722816 : ((((p4 → (False ∧ p5)) ∨ True) ∨ p3) ∧ (((((p2 ∧ p2) ∨ (p3 ∨ (False → (True ∨ (p5 ∧ (p1 ∧ (p3 ∧ p3))))))) ∧ p4) ∨ p5) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179169930897232929127043244911 : ((p2 ∧ (p1 ∨ ((p5 ∨ (True → (p4 ∧ ((p4 ∨ p1) ∨ p3)))) ∧ p4))) ∨ (((True ∨ (p2 → p2)) → ((True ∧ False) → (p5 → True))) ∨ p4)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608787933644669590142477380948 : ((((((p2 ∧ (p4 → (((False ∧ False) ∨ p3) ∨ (False ∨ ((p3 ∧ p5) ∧ ((p4 ∧ True) ∨ p4)))))) ∨ (True → (p2 ∨ True))) ∨ True) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134151886374139431620076474710 : ((((((p4 ∨ p2) → ((p2 ∨ p3) ∨ p1)) ∨ (((p4 → (p5 ∧ p3)) → p1) ∨ False)) ∨ (True ∨ (True ∨ True))) ∨ False) ∨ ((p3 ∧ True) ∧ True)) := by
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
theorem thm_5_vars_1506551453175805299325584203 : (((p5 → ((p5 ∧ (p4 ∧ (p1 ∨ ((p3 ∧ p1) ∨ (p3 ∨ (p1 ∧ p1)))))) → p5)) → (p1 → (p3 → (p1 → False)))) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42181365094140538394400746686 : (((True ∧ ((p3 ∨ (((((p2 ∧ (((False ∧ p5) → p5) ∨ p5)) ∨ True) → (p5 ∧ ((False ∧ p3) ∨ p3))) → p3) ∨ p1)) → False)) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320326397008044817711683207290 : (p4 ∨ ((p3 ∨ p4) ∨ (p3 → ((False ∧ (p5 ∨ True)) ∨ (p5 ∨ (p3 → ((p1 ∨ (p4 ∨ ((True ∧ False) ∧ p3))) → (False → (True ∧ p3))))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217503631118593133710873066849 : ((((p2 ∨ p2) ∧ p1) → p1) → ((((p2 ∨ p5) ∨ False) → (p4 ∨ False)) ∨ (((((p2 ∨ (p1 ∨ p1)) ∨ p3) → p5) ∨ (p2 ∨ p4)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218045106773480204466986601968 : (((p2 ∨ p3) ∧ (True ∨ p2)) → ((p2 ∨ ((p5 ∧ ((False → (True ∧ (True ∧ p2))) ∧ ((False ∧ (False ∨ (p5 ∧ p4))) ∧ p3))) ∨ p3)) ∨ p5)) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233883037447121056095808269255 : ((p4 ∨ (p1 ∨ p5)) → ((p4 ∧ False) ∨ ((p3 → (((p2 ∨ (True ∧ (((False ∧ ((p5 → p5) ∧ False)) → p2) ∧ False))) → False) ∨ p2)) ∨ True))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41832308575043602271866538391 : ((((False ∧ (p3 → False)) ∧ (((p4 ∧ (p2 ∧ p1)) ∧ (p1 ∧ p1)) ∨ (False ∨ (True ∧ ((p3 ∧ ((p4 → p5) ∧ p4)) ∨ p1))))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62521649956574321147118532090 : ((p3 ∧ (p5 ∧ ((p5 ∨ ((((p3 ∨ (((((p1 ∨ p4) ∧ (False ∧ True)) → (False → p5)) ∨ p3) → p4)) ∧ p1) ∧ False) ∨ p2)) ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



