variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198732278757303619572406344290 : ((p5 ∨ (p3 ∨ (p4 → (p5 ∨ (p3 ∧ p2))))) ∨ (p2 ∨ ((p4 ∧ False) → (((((True → (True ∨ p3)) ∧ p5) → p3) ∧ False) → (p5 ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_130775852286949051807145968328 : ((((p3 → (p5 → (((p4 → p2) ∨ (p5 ∧ p2)) ∨ (False → p2)))) → p1) ∨ (((p4 ∧ (p5 → False)) → p2) → True)) ∧ ((p4 ∧ p4) → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_688001853918604716081924040162 : (((((p5 → ((p4 ∧ False) → (p3 → p2))) ∧ (False → (((p3 ∨ True) → p4) ∨ False))) ∧ (((p5 → (p4 ∧ p3)) ∧ (False → p3)) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317347140788954364911582415376 : (p4 ∨ (((((p5 → False) ∧ p4) ∧ (((False ∧ (p5 ∧ False)) ∧ p5) ∧ (False → True))) ∨ (((p1 → False) ∧ ((True → p2) ∧ False)) → p2)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113919298555666984323966571416 : (((((p1 ∧ ((False ∨ p1) ∧ True)) ∨ ((p3 ∧ (False ∨ p4)) ∧ (True ∧ p1))) ∧ ((p2 ∧ True) ∧ p1)) ∧ ((p2 → p3) → False)) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38662581385821125229939474823 : ((((p3 → (((True ∧ (p5 ∨ p5)) ∨ p1) ∧ p5)) → (((p5 → ((p4 ∧ p4) → False)) → (False → (p3 → (False ∨ p3)))) → p4)) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148207260420537490195964059866 : (((False ∨ (True → (p1 ∨ ((p3 ∨ (p4 → True)) ∧ ((p3 ∨ (p1 ∨ True)) ∧ False))))) ∧ ((False → p2) → True)) ∨ ((p4 ∨ (p3 → True)) ∨ p4)) := by
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
theorem thm_5_vars_2180473170446092731911870679 : (((p2 → (False ∧ ((p1 ∨ (p1 ∧ (p5 → (p1 ∧ (p1 ∧ True))))) → p4))) ∨ False) ∨ (((p4 ∧ p5) ∧ (False → (True ∨ False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59923306438163487234338559066 : (((p5 ∧ p5) → (((((True ∧ ((((False → (p4 → ((True → p3) ∨ p3))) ∨ True) ∧ p3) ∧ p2)) → (p4 ∧ p1)) ∨ p1) ∧ p2) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244276709038474504375388280953 : ((False ∧ True) ∨ ((True → ((p5 ∨ (False ∧ p5)) ∧ p3)) → (p5 → (p3 → ((p2 ∧ p4) ∨ (p3 ∧ (((True → (p4 ∨ False)) ∨ p5) ∨ True))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4613515235502299082461877062 : (p4 → (False ∨ (((((True ∨ (p3 ∨ (p5 ∨ ((p5 → True) → p5)))) → ((p2 ∧ p2) ∧ p5)) ∧ (p5 ∨ p5)) ∧ (p5 ∨ False)) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157511225968127108642573968946 : (((p4 ∧ ((p1 ∨ ((p1 → p2) → (((p1 ∨ p3) ∧ p2) → True))) ∧ (p2 → p4))) ∨ (p4 ∨ p5)) ∨ ((True → ((p1 ∨ p2) ∧ p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62230632939318437483364153665 : ((p3 ∧ (((p2 → ((p4 → (p1 → (p4 ∧ p3))) ∧ (True → (False ∧ ((p3 ∧ (p5 ∨ (False → (p4 ∨ True)))) → p3))))) → p2) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_599856002195659038142556059439 : (((((p1 ∧ p3) → (((((p4 ∨ p5) ∧ p2) → p2) → (False → ((p2 ∧ (p1 ∧ (False ∨ (p4 → True)))) → (False ∧ p1)))) → p4)) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300376623881257811581667180568 : (False ∨ (((p2 ∨ ((False → p5) → (p5 ∧ (p3 ∨ (p4 ∨ (((False ∧ p2) → False) ∨ True)))))) ∧ (False ∨ (True ∧ True))) ∨ (False ∨ (True ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309409680994460938048454868521 : (p2 ∨ ((p3 → (((p1 ∧ False) ∧ (p2 → ((p3 ∧ p1) ∧ p1))) ∨ (True ∧ (False → (False ∧ ((p2 ∧ (p2 → False)) → p5)))))) ∨ (True ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337352735662542221540215594562 : (p1 → ((((p1 ∨ p3) ∨ ((((p4 ∨ ((p3 → p4) ∧ (((False ∨ p5) ∨ p2) → p4))) ∨ p1) ∧ p1) ∨ p5)) → p2) ∨ (p1 ∨ (p3 ∧ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306180594745212371978820619024 : (p1 ∨ ((p3 ∧ (p4 ∨ p5)) ∨ ((((p2 ∨ (p4 ∨ False)) ∨ p4) → ((True → p1) ∧ (((p2 ∧ False) ∧ (p1 ∧ p2)) ∨ p1))) ∨ (p4 → p4)))) := by
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
theorem thm_5_vars_219948569679195489190500972479 : ((p5 → ((p5 ∧ p5) ∧ p2)) → (((p2 ∧ ((p5 → p1) → ((p2 → p1) → p5))) → (((p1 ∨ False) ∨ p4) ∨ (p1 → (p1 ∧ p2)))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h5
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118685049571051254639425158025 : ((p5 ∨ (((False ∨ (p1 → p1)) ∧ (((p3 ∨ (((p5 → p3) ∨ p3) → ((p5 → (p5 ∨ p3)) → p1))) → p1) ∧ p5)) ∧ p2)) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135040519374619528477943762933 : ((((p4 ∨ (p5 ∧ (False ∨ ((((True ∧ p2) → p2) ∨ (False ∧ (p2 ∨ (p2 ∧ p4)))) ∧ p1)))) ∧ p3) ∨ (p4 → p4)) ∨ (True → (p4 ∧ p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_909035586316793642018288818828 : (((((((((p3 ∧ p1) → p5) → p4) ∨ (p4 ∧ p3)) ∨ p5) ∧ ((True → p1) ∧ (p5 → False))) ∧ (((True ∨ p5) ∧ (False ∨ p3)) ∧ p3)) → p1) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h5.left
      let h9 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h3.left
      let h11 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h10.left
      let h13 := h10.right
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h15 =>
          -- False on the left can always be used.
          apply False.elim h15
        case inr h16 =>
          -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
          have h17 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h8, we can now drive its conclusion.
          let h18 := h8 h17
          -- One of the premise coincides with the conclusion.
          exact h18
      case inr h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h20 =>
          -- False on the left can always be used.
          apply False.elim h20
        case inr h21 =>
          -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
          have h22 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h8, we can now drive its conclusion.
          let h23 := h8 h22
          -- One of the premise coincides with the conclusion.
          exact h23
    case inr h24 =>
      -- Conjunctions on the left can always be decomposed.
      let h25 := h24.left
      let h26 := h24.right
      -- Conjunctions on the left can always be decomposed.
      let h27 := h5.left
      let h28 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h29 := h3.left
      let h30 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h31 := h29.left
      let h32 := h29.right
      -- Disjunctions on the left can always be decomposed.
      cases h31
      case inl h33 =>
        -- Disjunctions on the left can always be decomposed.
        cases h32
        case inl h34 =>
          -- False on the left can always be used.
          apply False.elim h34
        case inr h35 =>
          -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
          have h36 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h27, we can now drive its conclusion.
          let h37 := h27 h36
          -- One of the premise coincides with the conclusion.
          exact h37
      case inr h38 =>
        -- Disjunctions on the left can always be decomposed.
        cases h32
        case inl h39 =>
          -- False on the left can always be used.
          apply False.elim h39
        case inr h40 =>
          -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
          have h41 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h27, we can now drive its conclusion.
          let h42 := h27 h41
          -- One of the premise coincides with the conclusion.
          exact h42
  case inr h43 =>
    -- Conjunctions on the left can always be decomposed.
    let h44 := h5.left
    let h45 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h46 := h3.left
    let h47 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h48 := h46.left
    let h49 := h46.right
    -- Disjunctions on the left can always be decomposed.
    cases h48
    case inl h50 =>
      -- Disjunctions on the left can always be decomposed.
      cases h49
      case inl h51 =>
        -- False on the left can always be used.
        apply False.elim h51
      case inr h52 =>
        -- We want to use the implication h44 based on <expert-advice>. So we show its premise.
        have h53 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h44, we can now drive its conclusion.
        let h54 := h44 h53
        -- One of the premise coincides with the conclusion.
        exact h54
    case inr h55 =>
      -- Disjunctions on the left can always be decomposed.
      cases h49
      case inl h56 =>
        -- False on the left can always be used.
        apply False.elim h56
      case inr h57 =>
        -- We want to use the implication h44 based on <expert-advice>. So we show its premise.
        have h58 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h44, we can now drive its conclusion.
        let h59 := h44 h58
        -- One of the premise coincides with the conclusion.
        exact h59
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137975516093140731426246582819 : ((p5 ∨ ((((False ∧ (p1 ∨ p3)) ∧ p1) → p3) ∧ (((p3 → p4) ∧ (p2 ∨ p1)) → ((p5 → True) → (p5 ∧ p3))))) ∨ ((True → True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39456930589900184375133385168 : (((p5 ∧ ((p1 ∨ False) ∧ (((p5 ∧ (True ∧ p3)) ∨ p3) ∨ (False → ((p5 → p5) ∧ (p5 → ((False → p1) → (p5 → p2)))))))) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56563688682839850425467775585 : (((p5 ∨ ((p4 → p4) ∨ p2)) → ((p4 → (p4 ∧ (False ∨ ((((p5 ∧ p5) ∨ (p1 → p4)) ∨ (p2 ∧ False)) ∧ p1)))) → (True → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610689189724746840550925185481 : ((((((True ∨ (p3 → (((p3 ∨ (p4 ∧ p5)) ∨ p5) ∨ (((p2 ∨ (p4 ∨ True)) ∧ p2) ∧ p3)))) ∧ (True ∧ (p4 → p4))) → p3) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263197020524044182549052193345 : (True ∧ ((((p3 ∧ (((((((p4 → p1) → p2) ∨ (p4 ∧ False)) → (p4 → p3)) ∧ (p1 → p4)) ∨ p2) ∨ False)) → p2) ∨ p5) → (p2 ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172123693898243300480168473297 : ((((p5 → (((p5 → p4) → p2) → (p5 → p1))) → False) ∧ ((True → p5) ∧ p3)) ∨ ((p5 ∧ (False ∨ ((False → p5) ∨ False))) → (True ∨ p4))) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205080758500933397613743186870 : (((p5 → (True ∨ (p4 → p3))) → False) ∨ (True → (((p4 ∨ (p5 ∧ (p3 → (p1 → ((False ∨ False) ∨ ((True ∧ p5) ∨ p2)))))) ∨ False) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199074944488690212490823026791 : (((((p4 ∧ p2) ∧ (p5 ∧ True)) → True) ∧ p4) → ((((p5 ∨ True) → (p5 ∨ ((p4 → p2) → p5))) ∨ (p1 ∨ p5)) ∨ (p3 → (p2 ∨ p3)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303915224118051623867556594254 : (p1 ∨ ((((p1 ∧ (p4 ∧ (p3 → p4))) ∨ ((p2 ∨ (False ∨ True)) → p4)) → (p2 → (True ∧ ((True → ((p2 ∧ p3) ∨ False)) ∧ p4)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136121548601285662074593732948 : (((p2 ∨ (p1 ∧ ((p3 ∧ p2) ∨ (True ∧ True)))) ∨ ((p4 ∧ (p3 ∨ ((False → (False ∧ p5)) ∨ p2))) ∨ (p4 ∧ p4))) ∨ ((p2 → True) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358717633680984000936000132441 : (p5 → (p5 → (((((((p1 → ((False ∨ p4) ∨ p1)) ∧ (True ∨ p3)) ∨ True) → (p3 → True)) → p4) ∧ (p4 ∨ p3)) ∨ ((False → p4) ∧ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356619778034232515938286765837 : (p5 → ((((p2 → p1) ∨ (p5 ∨ (p5 ∨ p1))) → False) ∨ (p2 ∨ ((p5 ∨ ((p2 ∨ p1) ∧ (((True ∨ p4) ∧ p2) ∧ False))) → (p1 → p5))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h7.left
      let h10 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h9.left
      let h12 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h13 =>
        -- False on the left can always be used.
        apply False.elim h10
      case inr h14 =>
        -- False on the left can always be used.
        apply False.elim h10
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h7.left
      let h17 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h18 := h16.left
      let h19 := h16.right
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h20 =>
        -- False on the left can always be used.
        apply False.elim h17
      case inr h21 =>
        -- False on the left can always be used.
        apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_741460773114374839706195260028 : ((((p5 ∨ p2) ∨ (((p2 ∨ p1) ∧ (((p1 ∨ ((((p5 ∧ p5) ∨ p3) → p5) → False)) ∨ (((p1 ∨ p2) ∧ p2) ∨ False)) → p3)) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258678561347233280084517560811 : ((p5 ∨ p5) → ((False → True) → (((p2 ∧ p1) → p5) ∧ ((False ∧ (True → (((False ∧ (p3 → (p5 ∨ (False ∧ p2)))) ∧ p4) ∨ p1))) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h7
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258402352290065893895230156352 : ((p5 ∨ p1) → ((p5 ∧ (((True ∨ p5) → ((p2 → (((p2 ∨ p3) ∨ (p3 ∧ p4)) → p2)) ∧ ((p5 ∨ (p1 → p4)) ∧ False))) ∧ p5)) ∨ True)) := by
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
theorem thm_5_vars_184176755667291878220307577349 : (((p2 → (((p3 ∨ p1) ∨ p5) ∨ (p1 ∨ (True → p3)))) ∨ True) ∨ (((p3 → False) ∨ p2) ∧ (((p2 ∧ ((p4 → p5) ∨ p2)) → p3) ∨ True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43572987724213084849184762359 : (((((p2 → (((p1 → False) ∧ ((p3 ∨ ((p4 → False) → True)) ∨ False)) ∧ (((p5 → (p4 → True)) ∧ True) → True))) ∧ p4) → p3) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_717636771700859319617339324111 : ((((p5 → ((False ∧ False) → p5)) ∧ ((((p5 ∨ True) → True) ∧ ((False ∧ p4) ∨ ((p5 → p3) → False))) ∨ ((p4 ∧ p4) → (p1 ∨ True)))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255545358938898008184164805968 : ((p5 ∧ p3) → ((((p1 ∨ ((True → p1) ∨ False)) ∧ ((p3 → ((p3 → False) → (((p1 ∨ False) ∨ p3) ∨ False))) ∧ True)) ∨ (p3 → p5)) ∨ p3)) := by
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
theorem thm_5_vars_135604887854496374553795945155 : ((((p4 ∧ p2) ∨ (p5 ∨ (p2 ∨ (False ∨ (p2 → (p4 ∧ ((p1 ∧ p5) ∧ p2))))))) ∨ (p4 ∧ ((True ∨ p2) → False))) ∨ ((True → False) → p3)) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_384780421749228695909003134220 : ((((((p5 → p3) ∨ (False ∨ ((p1 ∨ (p2 ∨ ((p2 ∧ ((p5 ∧ (False ∨ p1)) → (p3 ∨ (False → p5)))) ∧ p3))) → True))) → p5) ∨ True) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119789819678157230565248744037 : ((((((False → p5) → (p1 ∨ ((p2 ∧ (p4 ∧ p3)) ∨ ((False ∨ (p4 → p4)) ∨ (p4 ∨ (p4 → False)))))) ∨ False) → False) ∧ p5) → (p2 ∧ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (((False → p5) → (p1 ∨ ((p2 ∧ (p4 ∧ p3)) ∨ ((False ∨ (p4 → p4)) ∨ (p4 ∨ (p4 → False)))))) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h4
  -- False on the left can always be used.
  apply False.elim h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h10 : (((False → p5) → (p1 ∨ ((p2 ∧ (p4 ∧ p3)) ∨ ((False ∨ (p4 → p4)) ∨ (p4 ∨ (p4 → False)))))) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h11
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- One of the premise coincides with the conclusion.
    exact h12
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h13 := h8 h10
  -- False on the left can always be used.
  apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121428080171788492771683934513 : ((((p3 → ((p5 ∧ (p1 → (p3 ∧ p2))) ∨ (((p4 → (p3 ∧ (p1 ∧ ((p1 ∧ True) ∧ p3)))) ∨ p3) ∨ p2))) ∨ p1) → p1) → (p1 ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p3 → ((p5 ∧ (p1 → (p3 ∧ p2))) ∨ (((p4 → (p3 ∧ (p1 ∧ ((p1 ∧ True) ∧ p3)))) ∨ p3) ∨ p2))) ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57420717266588206146762855345 : (((p2 ∨ (False ∨ p5)) ∨ ((True ∧ ((p3 → ((p1 → p1) → (((p5 ∧ False) ∧ p5) → False))) → ((p4 → False) ∨ (p4 → True)))) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63130804723831179461985706827 : ((p5 ∧ (((p5 → ((p4 → (p2 → p3)) ∧ False)) ∧ ((False ∨ (((p5 ∧ p5) ∧ p5) ∨ ((p4 → (p3 ∨ True)) ∨ p3))) ∧ p4)) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171588238028989564862584523914 : ((((p4 ∨ (((p2 ∧ True) → (p2 ∨ p3)) ∧ False)) ∧ (p3 → (p3 ∨ p3))) ∨ False) ∨ ((False ∨ ((p2 ∨ p3) ∧ p5)) ∨ (p2 → (p3 → True)))) := by
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
theorem thm_5_vars_173793805216048979871377642597 : (((True ∧ (p1 ∧ (p2 ∨ ((p4 ∨ ((p4 → True) ∨ (p1 ∧ p4))) ∨ p2)))) ∨ p2) → (((((p2 ∨ (p4 → True)) → False) ∧ p4) ∧ p5) → p2)) := by
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
  cases h1
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
          have h16 : (p2 ∨ (p4 → True)) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h17
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h5, we can now drive its conclusion.
          let h18 := h5 h16
          -- False on the left can always be used.
          apply False.elim h18
        case inr h19 =>
          -- Disjunctions on the left can always be decomposed.
          cases h19
          case inl h20 =>
            -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
            have h21 : (p2 ∨ (p4 → True)) := by
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Implications on the right can always be decomposed.
              intro h22
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h5, we can now drive its conclusion.
            let h23 := h5 h21
            -- False on the left can always be used.
            apply False.elim h23
          case inr h24 =>
            -- Conjunctions on the left can always be decomposed.
            let h25 := h24.left
            let h26 := h24.right
            -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
            have h27 : (p2 ∨ (p4 → True)) := by
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Implications on the right can always be decomposed.
              intro h28
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h5, we can now drive its conclusion.
            let h29 := h5 h27
            -- False on the left can always be used.
            apply False.elim h29
      case inr h30 =>
        -- One of the premise coincides with the conclusion.
        exact h30
  case inr h31 =>
    -- One of the premise coincides with the conclusion.
    exact h31



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174777762218505760749153717352 : (((p5 ∧ p3) ∧ (p2 ∧ (True ∧ (True ∨ ((p3 ∨ (p5 → (p2 ∧ p5))) ∨ p4))))) → (p1 → ((p4 ∨ False) ∨ (p1 → (p3 → (p3 ∨ p3)))))) := by
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
  let h7 := h4.left
  let h8 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- Implications on the right can always be decomposed.
    intro h13
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h13
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h17
        -- Implications on the right can always be decomposed.
        intro h18
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h18
      case inr h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h20
        -- Implications on the right can always be decomposed.
        intro h21
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
      exact h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_750146560001268084735004719956 : (((True ∧ ((p5 → (((p4 ∧ p3) ∨ ((((p1 ∧ ((p1 ∧ p3) ∧ p3)) → p4) → False) → (((p2 ∧ False) ∧ p5) ∧ p5))) ∧ True)) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157922363978500153605430982585 : (((p2 → ((p3 ∨ False) ∨ (p5 ∨ ((False → True) ∧ p1)))) → ((True ∧ (p2 ∨ p2)) → (True → p1))) ∨ (((p2 ∨ (False → p3)) ∨ True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_154712272988298405639159992679 : ((((p5 → ((p3 ∨ (p1 → (p4 ∨ (True → ((False ∨ p2) ∨ p5))))) ∨ p2)) ∧ True) ∨ (True ∨ p2)) ∧ (p1 ∨ ((p1 → p4) → (p5 → True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198052925922725027569777143659 : (((p4 ∧ p3) ∨ ((p3 ∨ p1) ∧ (p3 ∨ p3))) ∨ (((True ∨ p2) ∧ False) ∨ ((p3 → p3) ∨ (((False ∧ p5) ∨ ((False ∧ p2) ∨ True)) ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148975206434623629157508549168 : ((((p4 → p2) → False) ∧ ((p5 ∨ (p2 → ((p3 → (p2 ∧ p5)) ∧ False))) ∧ (p3 ∨ ((p3 ∧ True) ∧ p1)))) ∨ (True ∨ (p3 ∨ (p1 ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249969971847641299041003781782 : ((True → p2) ∨ (((p5 ∨ ((False ∨ (((p3 ∧ False) → p5) → False)) ∧ (p1 → p4))) ∨ (p4 ∨ ((True ∨ p5) ∨ (p2 ∨ False)))) ∨ (p1 ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_174955650122599586441963201187 : ((True ∧ ((p3 → (p1 ∧ (((((p1 ∨ p1) ∧ False) → p2) ∨ False) → p4))) → p1)) → (True → (p4 → (True → ((p2 → p5) ∨ (p5 → p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h7
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191000106978752374146524910460 : ((((False → p2) → (p1 ∨ p5)) ∨ (True ∧ (p2 → p4))) ∨ (((True ∨ (p4 ∧ p1)) → (((p1 ∨ p5) → (p2 ∧ p4)) → p1)) ∨ (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177485454245431798700250663875 : ((p1 → (((p1 ∧ (p1 ∨ (p5 → (p3 ∨ True)))) ∨ (p4 ∨ p3)) → True)) ∧ (p3 → ((True ∧ False) ∨ ((p1 ∨ p4) ∨ (p5 ∨ (p4 ∨ p3)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303232952750633836880111560506 : (False ∨ (p5 → ((((p5 ∧ p5) → p2) ∧ ((p5 ∨ p2) ∧ ((((p5 ∧ p4) ∧ p4) ∨ (p5 → (p4 ∧ ((True ∨ p4) ∨ p1)))) → p5))) → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  cases h5
  case inl h7 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h8 : (p5 ∧ p5) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h1
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h9 := h3 h8
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51824142090305503011261340403 : (((p2 → ((p2 ∧ False) ∧ (((False → p3) ∧ ((p4 → (p2 ∨ p5)) ∧ False)) ∧ p3))) ∧ ((p3 ∧ (((p4 → p1) → p3) ∧ p4)) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617839399244450308597921649673 : (((((((True ∨ (p1 ∧ p5)) ∨ False) → p3) → (((p1 → (((p2 ∨ p5) ∨ p3) → (((p2 ∨ p4) ∧ p5) ∨ p3))) ∧ p5) ∨ True)) ∨ p3) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225031047011301478469096453286 : (((False ∧ p2) ∧ p4) ∨ ((True → ((((False ∨ (((p1 → p3) ∨ p5) → p2)) ∧ p5) ∧ (p4 → (p5 → False))) → (p5 → (True ∧ p2)))) ∨ p1)) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : ((p1 → p3) ∨ p5) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h11 := h9 h10
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678111217847089319362065015747 : ((((((((p1 → True) → (p2 ∨ p1)) ∧ p2) ∨ (p4 → (False ∨ p3))) ∧ (((p5 ∧ p5) ∧ p4) ∨ False)) ∨ (False → (False → (False ∨ p3)))) ∨ p1) ∧ True) := by
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
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178438284367699300744858255050 : (((((p4 ∧ (True ∧ (False ∧ p5))) → p5) → p3) ∧ (p4 → (True ∨ False))) ∨ ((p5 ∨ ((p4 ∧ ((p2 → p3) → p2)) ∧ p1)) ∨ (True → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351550220551114057990617336775 : (p4 → ((p1 → (p2 ∧ (False ∨ (p3 ∧ (((p2 ∧ (p3 ∧ ((p1 ∨ False) ∧ False))) ∨ True) ∧ p4))))) ∨ (((p2 ∨ False) ∨ p4) → (p4 ∨ True)))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h5 =>
      -- False on the left can always be used.
      apply False.elim h5
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135689020086364375475139650927 : (((((p4 → (p5 → p3)) ∧ ((p4 → (False → (p5 → p3))) ∧ p1)) → False) ∧ (True ∨ (((p5 → p4) → p1) ∨ p1))) ∨ (True ∨ (True → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263979638883708393475899394957 : (True ∧ ((((False → (False → ((p1 ∨ p4) ∧ p2))) ∨ p5) → (False ∨ p5)) ∨ ((p3 ∧ (True ∧ (((p4 ∨ p2) → p3) ∧ False))) → (p5 ∨ p1)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52675489050315989620240784677 : (((p1 ∨ (True ∧ ((p4 → (True → (p1 → p2))) ∧ (p5 → (p5 → False))))) ∨ (True ∧ (p1 → ((p1 → ((True ∧ p1) ∨ True)) → False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205474254610750523599637984181 : (((p5 → (True → p5)) → (True → p2)) ∨ ((p2 ∨ p3) → ((p5 ∨ p2) ∨ (((False ∨ ((p1 ∧ p3) ∨ True)) ∨ (p3 ∧ p2)) ∨ (p4 → p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
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
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44658289194306001212183346693 : ((((p2 ∧ (False → ((True ∨ p3) → p5))) ∨ (((p1 → (p3 → (((p3 ∧ (True ∧ (True → p2))) ∨ p4) → True))) ∧ p4) ∧ p1)) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304996766449179125847912052400 : (p1 ∨ (((p3 ∨ ((True → (p1 ∧ ((p2 ∨ ((p5 ∧ (p1 → (p1 ∧ p3))) → p1)) ∨ p3))) ∧ True)) ∨ (False → True)) ∨ (False ∧ (p4 → p5)))) := by
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
theorem thm_5_vars_148641628642610741782344300825 : (((((p3 ∧ (False ∧ False)) ∨ (False → p4)) ∨ True) ∧ ((p5 ∨ (False ∨ p2)) ∨ (p4 → ((p1 → True) ∨ p1)))) ∨ (((p4 ∧ p4) ∧ p5) ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111922864709430511828856692421 : (((((p3 ∧ (p5 → (True → p5))) → (((True ∧ p1) ∨ p4) ∨ p5)) → (((p2 → False) ∧ p3) ∧ (p2 ∧ (p5 → p3)))) ∨ p3) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60122561532688295420059780534 : (((p3 ∨ p5) → ((True → (p5 ∧ (((p2 ∨ (p5 ∨ (p3 → ((p5 → p1) → True)))) → False) ∧ p2))) → (((p5 → True) → p3) ∧ p2))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h6
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- We need to get the left conjuct of h8 based on <expert-advice>.
    let h9 := h8.left
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : (p2 ∨ (p5 ∨ (p3 → ((p5 → p1) → True)))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h11 := h9 h10
    -- False on the left can always be used.
    apply False.elim h11
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h12 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h13 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h14 := h2 h13
    -- We need to get the right conjuct of h14 based on <expert-advice>.
    let h15 := h14.right
    -- We need to get the right conjuct of h15 based on <expert-advice>.
    let h16 := h15.right
    -- One of the premise coincides with the conclusion.
    exact h16
  case inr h17 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h18 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h19 := h2 h18
    -- We need to get the right conjuct of h19 based on <expert-advice>.
    let h20 := h19.right
    -- We need to get the right conjuct of h20 based on <expert-advice>.
    let h21 := h20.right
    -- One of the premise coincides with the conclusion.
    exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38169934842343676870975246819 : (((((True ∨ ((True ∨ (p2 ∨ (p2 ∧ p5))) ∧ p5)) → ((((p1 ∧ p4) → False) → (p2 ∨ p1)) ∧ p1)) ∨ (False ∨ (p4 ∧ p5))) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323739268379605350354269240687 : (p5 ∨ ((p5 → (p1 ∨ (((p3 ∨ (p2 ∧ p3)) → p1) → ((((p3 ∨ False) ∧ p1) → p4) → (p5 ∨ p1))))) → ((p4 ∧ p3) ∨ (False → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215262626700193124753042190453 : ((False ∧ (False ∨ (p1 ∧ p1))) ∨ (((p4 ∧ p1) → (((True → (True ∧ (p4 ∨ p5))) → ((p3 ∧ p2) ∨ p5)) ∨ ((p5 → p3) ∨ p1))) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699882182031172016161925299191 : ((((((False → ((True → False) ∧ True)) ∧ p3) ∨ ((p3 ∨ p4) ∨ p1)) → (p2 ∨ ((p4 ∨ (((p4 → True) → (False → p1)) ∨ p5)) ∨ p1))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h6
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h10
        -- Implications on the right can always be decomposed.
        intro h11
        -- False on the left can always be used.
        apply False.elim h11
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h12
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_733818539940254668515883024758 : ((((p5 ∧ p4) ∧ ((((True ∧ ((((False ∧ ((True ∧ p3) ∨ p5)) ∨ (p4 ∧ p2)) ∨ True) ∨ ((p4 ∨ p5) ∨ p1))) ∧ True) ∧ p5) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306318279852550576318880574456 : (p1 ∨ ((False ∨ True) ∧ (p3 → ((((True ∨ (True ∧ (p5 ∨ p1))) ∧ ((p2 ∧ p4) ∨ p3)) → (((True ∨ False) ∨ (p2 ∧ p4)) ∧ False)) → p4)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((True ∨ (True ∧ (p5 ∨ p1))) ∧ ((p2 ∧ p4) ∨ p3)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221135828069092234234006379098 : (((True ∨ p3) ∨ True) ∧ ((p2 ∨ (((p2 ∨ (p3 → ((p4 ∨ p2) → ((False ∨ (True ∧ p2)) ∨ p2)))) ∨ (False → p4)) ∨ (True ∨ p1))) ∨ p5)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_779830238584470772077757931532 : (((p2 ∨ (((p5 → p2) → (p1 ∧ ((((p2 ∧ (p3 ∧ p5)) → p5) ∧ p1) ∨ (((p5 ∨ (p4 → p4)) ∨ (p4 ∧ p4)) → p1)))) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325776895084315523516913949585 : (p5 ∨ (p2 ∨ (False ∨ (((p4 ∨ (p3 ∨ (((p3 ∨ (p1 → p3)) ∧ ((p5 → False) ∨ False)) ∧ p5))) → p1) → ((p1 ∨ (p3 → p2)) ∨ True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_927571624817327418012260148336 : ((((((True ∨ (False ∧ (True → (p5 → False)))) ∨ p2) → False) ∧ (True ∨ ((p2 → (p1 → (p1 ∨ (p3 ∧ p3)))) ∧ ((p3 ∨ False) ∨ p1)))) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : ((True ∨ (False ∧ (True → (p5 → False)))) ∨ p2) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h12 : ((True ∨ (False ∧ (True → (p5 → False)))) ∨ p2) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h13 := h2 h12
        -- False on the left can always be used.
        apply False.elim h13
      case inr h14 =>
        -- False on the left can always be used.
        apply False.elim h14
    case inr h15 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h16 : ((True ∨ (False ∧ (True → (p5 → False)))) ∨ p2) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h17 := h2 h16
      -- False on the left can always be used.
      apply False.elim h17
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_169468158373969302922778677107 : ((((p1 → ((p1 ∧ p5) ∧ p1)) ∧ ((p1 → p5) → ((p1 ∧ p3) ∨ p1))) ∨ True) ∧ ((p3 → (p1 → p1)) ∨ (p5 ∨ (True ∧ (p4 → False))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678338178866468053259898666241 : ((((((True ∨ p4) → (p3 → (p3 ∨ p5))) ∧ ((p2 ∧ (p2 ∧ (p3 ∧ p5))) ∧ (p2 → (p1 → False)))) ∨ ((False ∧ p2) ∧ (p5 → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39082822850420172434793452931 : ((((p3 ∨ p2) ∨ ((((p2 → p3) → ((p5 ∧ (((p5 ∨ p5) ∨ ((p4 → (p1 → p3)) ∨ False)) ∨ False)) ∨ True)) ∨ True) ∨ False)) ∧ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_154741444093348486789656594397 : ((((((p3 → (False ∨ p4)) → p5) ∨ p2) ∧ (((True → (p2 ∨ p3)) ∨ True) ∧ True)) ∨ (True → True)) ∧ (p5 → ((p4 ∧ p5) ∨ (p1 → p1)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133834584936446558915396093167 : ((((False ∨ p2) → (((p1 ∨ (False ∧ (False ∧ (((p2 ∨ (False ∧ p1)) → (p5 ∨ p1)) → p4)))) ∨ p4) ∧ p5)) ∧ p4) ∨ ((True → False) → p5)) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148927391959069957062921548625 : ((((p4 → p1) ∧ (p3 ∧ p1)) → ((p5 ∨ ((((True ∨ p5) → (p4 → p4)) ∧ p2) ∨ (p4 ∧ p2))) ∧ p2)) ∨ ((True ∧ (p3 ∧ p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183769238282557341241247265734 : ((((((p2 ∧ False) ∨ (True ∧ (True → p5))) ∧ False) ∧ p3) ∧ p4) ∨ (p3 ∨ (((((((p4 ∨ p4) ∨ p2) ∨ True) ∨ p1) ∨ True) → p5) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231995227615820963925129895940 : (((p2 ∨ p2) → False) → (((False ∧ p1) ∨ p2) ∨ (((p1 → True) → ((p4 → True) ∧ ((p3 ∧ (True → p4)) ∨ (True ∨ (p3 ∧ p3))))) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232965369835669219195790246710 : ((p3 ∧ (True → p4)) → ((p3 → (((p2 ∨ p1) → ((p2 ∨ (p2 ∨ (False → ((p5 → p3) ∨ (p1 → True))))) → p2)) ∨ True)) ∧ (True ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_381879752457670515456332958313 : ((((((((((False ∧ (p4 ∨ p5)) → p4) ∧ ((p1 ∨ (p1 → p4)) ∨ (p1 ∨ (p4 ∧ False)))) ∧ (False → p3)) ∧ p5) → p1) ∨ p2) ∨ True) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156846399498597304693061343955 : (((p4 → ((((((p2 ∧ p5) ∧ p4) ∨ (False → p3)) ∧ p3) → (p5 → (p3 → p1))) ∨ p3)) ∧ p1) ∨ (False → (p4 ∨ ((False → True) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47771322313744612213013261067 : ((((p3 ∨ (p4 → (p5 → (((((True ∨ (True → (p4 ∨ p1))) ∧ p2) ∨ p4) ∧ (p5 ∨ p1)) ∧ (True → False))))) ∨ p2) → (p4 ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_631661013740039093952030494374 : ((((((p3 ∨ (p3 ∨ ((p4 → (p5 → (p5 ∧ p1))) → (p5 → (p5 → p5))))) ∧ (p3 ∧ (((p3 ∨ p2) ∨ p5) ∧ p5))) → True) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62087041203374616076164345836 : ((p2 ∧ (p3 ∧ ((((((p4 ∧ p4) → (p4 → ((p2 → p3) ∧ p3))) ∧ p1) ∨ (p1 ∨ p5)) ∧ (p3 → p2)) → ((p5 ∨ p3) ∨ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171437947258256709246149302131 : ((((p1 → p3) → ((True → ((p3 ∧ True) ∧ ((p4 ∧ False) ∧ False))) ∧ False)) ∧ p2) ∨ (False → ((p5 ∧ ((p3 ∧ (p4 ∧ p5)) → True)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



