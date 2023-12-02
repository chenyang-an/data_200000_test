variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135723309285415789262667998912 : (((((((p2 → True) ∧ ((p3 ∨ True) ∨ p4)) → (True ∧ False)) → p4) ∧ p1) ∨ ((False → p4) ∧ (True ∧ (p3 → p2)))) ∨ (False → (True ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244675447593339120089384526111 : ((p1 ∧ True) ∨ (((p4 → (False → ((p3 ∨ p4) ∨ (((p4 → True) ∨ (p5 ∧ p5)) → p1)))) ∧ (p1 ∨ (((p2 ∨ p2) ∨ p5) → False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326764062565441738442269113910 : (True → ((p3 ∨ (((p4 ∨ p5) → ((p1 ∨ False) ∧ ((p4 ∨ p4) ∧ (p4 ∨ (p4 ∨ (True → (((p5 ∨ p4) ∨ p4) → p3))))))) ∨ True)) ∧ True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172587972952724833685948695904 : ((((False → p3) ∨ p5) → ((p2 → (((p3 → p1) ∧ (p2 ∧ p3)) ∧ p3)) ∧ p3)) ∨ (True → ((True → ((p1 ∧ p5) ∨ (True ∨ True))) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_798511996419941469621472970922 : (((p1 → ((((p5 → (False → (p3 → False))) → p5) ∨ False) ∨ ((p3 → ((False → p4) ∨ p4)) ∨ (p5 ∨ ((p2 ∧ p1) ∧ (p1 ∨ False)))))) ∨ False) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621135712041255467827654398599 : (((((p5 → True) → ((p5 ∨ ((p1 ∨ p3) ∨ p5)) ∨ (p4 ∨ (True → (((p1 ∧ p5) ∨ True) ∧ (False ∨ ((True → True) ∧ True))))))) ∨ p2) ∨ p1) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149609760601973344387507065660 : ((p3 ∧ ((p2 ∨ p2) ∨ ((p3 ∨ ((p3 ∨ (p3 ∧ p3)) → False)) ∨ ((p4 → (p3 ∨ p2)) ∨ (True → False))))) ∨ (p4 → (p5 → (False → p1)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328164645081276728851274495785 : (True → ((((p3 → (p4 ∨ (p5 ∨ (((p4 → (p1 → ((False → False) → p1))) → p2) → p2)))) → (p5 ∧ p3)) ∨ p3) → (p3 ∨ (p4 ∧ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : (p3 → (p4 ∨ (p5 ∨ (((p4 → (p1 → ((False → False) → p1))) → p2) → p2)))) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h7 : (p4 → (p1 → ((False → False) → p1))) := by
        -- Implications on the right can always be decomposed.
        intro h8
        -- Implications on the right can always be decomposed.
        intro h9
        -- Implications on the right can always be decomposed.
        intro h10
        -- One of the premise coincides with the conclusion.
        exact h9
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h11 := h6 h7
      -- One of the premise coincides with the conclusion.
      exact h11
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h12 := h3 h4
    -- We need to get the right conjuct of h12 based on <expert-advice>.
    let h13 := h12.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h13
  case inr h14 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165463936269245216488465133818 : ((((p4 → p5) → (p3 ∧ (True → (p3 ∧ (True ∧ True))))) ∧ ((False ∨ (p1 → True)) ∧ p1)) ∨ (((p1 ∨ (p3 ∨ p5)) → p1) ∨ (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_598126733551908872409334822985 : ((((((p3 ∨ p3) ∧ p4) ∨ (p4 ∨ (p2 → (p5 → ((p4 ∧ p3) ∧ ((p3 → ((True ∨ (p4 ∧ p3)) → (p3 → p3))) ∧ p4)))))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305296663201456536563840521051 : (p1 ∨ (((((((p3 ∧ (True → (True ∧ p3))) ∨ p1) ∧ (p5 ∨ p3)) ∨ p5) → False) ∨ (True ∧ True)) ∨ ((True ∨ (p5 → (True → True))) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_503665310376710800519459321 : ((((((p5 ∧ False) → (p2 ∧ p2)) → ((((p5 → (p2 ∨ p1)) ∨ p5) ∨ p2) ∨ p2)) → ((False ∧ (p1 ∨ False)) ∨ p4)) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167289582019545363563215017167 : ((((p5 ∧ ((p5 ∨ ((True ∧ p4) → ((p2 → (False ∧ True)) ∧ True))) → p1)) ∨ p4) → p3) → ((p5 ∧ ((False → False) → p4)) → (p5 → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : (False → False) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h8 := h5 h6
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113498078280644136804234405047 : ((((True → ((p5 ∨ False) ∧ (p4 ∨ ((p4 → False) → (p5 → ((False → p3) → p2)))))) ∨ ((False ∧ True) → p3)) ∨ (p3 ∧ p1)) ∨ (p2 → p4)) := by
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
theorem thm_5_vars_328914269451918626003546856992 : (True → (((False ∧ (True → ((p2 → p2) → p2))) → p1) → ((True ∧ (p1 → (((True → p3) ∨ (p3 → ((p3 ∧ True) ∧ True))) → p5))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49948407211493636252944439063 : ((((((p5 → p3) → (True → ((p1 → p4) ∧ True))) → ((False ∨ p4) ∧ (p2 ∨ p4))) ∨ (p5 → p4)) ∧ ((p3 → (p3 ∧ p2)) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157708946427455055944333043927 : (((((((((True ∧ False) → p3) → p1) ∨ p3) ∧ False) ∨ p4) → (p1 ∨ p1)) → (p5 ∧ (p3 ∧ False))) ∨ ((p3 ∨ (True → p1)) → (p2 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64835165518693323237885856147 : ((p2 ∨ (((p2 ∧ True) ∧ (((p2 → (p3 ∧ ((False ∧ True) ∧ False))) → ((p1 ∧ (False ∧ (p1 → (p3 ∨ p3)))) ∧ True)) ∨ p3)) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_686099244745286910078143756664 : (((((p4 ∨ (((p1 ∧ (p2 → p3)) ∨ ((True → p3) ∧ p4)) ∨ False)) ∧ ((p1 ∧ p4) ∨ p3)) → ((p3 ∧ (p5 → p4)) ∨ (True ∨ p4))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h14 =>
          -- Conjunctions on the left can always be decomposed.
          let h15 := h14.left
          let h16 := h14.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h17 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h18 =>
        -- Conjunctions on the left can always be decomposed.
        let h19 := h18.left
        let h20 := h18.right
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h21 =>
          -- Conjunctions on the left can always be decomposed.
          let h22 := h21.left
          let h23 := h21.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h24 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h25 =>
      -- False on the left can always be used.
      apply False.elim h25
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142270368289062695297967626633 : ((p2 ∧ (((p1 ∧ ((p4 ∨ False) ∨ (True → p4))) ∨ (p5 ∨ p4)) ∧ ((p3 ∧ False) ∨ ((False → (True → True)) ∨ p2)))) → ((p2 → False) → False)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h12 =>
          -- Conjunctions on the left can always be decomposed.
          let h13 := h12.left
          let h14 := h12.right
          -- False on the left can always be used.
          apply False.elim h14
        case inr h15 =>
          -- Disjunctions on the left can always be decomposed.
          cases h15
          case inl h16 =>
            -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
            have h17 : p2 := by
              -- One of the premise coincides with the conclusion.
              exact h3
            -- We have shown the premise of h2, we can now drive its conclusion.
            let h18 := h2 h17
            -- False on the left can always be used.
            apply False.elim h18
          case inr h19 =>
            -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
            have h20 : p2 := by
              -- One of the premise coincides with the conclusion.
              exact h19
            -- We have shown the premise of h2, we can now drive its conclusion.
            let h21 := h2 h20
            -- False on the left can always be used.
            apply False.elim h21
      case inr h22 =>
        -- False on the left can always be used.
        apply False.elim h22
    case inr h23 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h24 =>
        -- Conjunctions on the left can always be decomposed.
        let h25 := h24.left
        let h26 := h24.right
        -- False on the left can always be used.
        apply False.elim h26
      case inr h27 =>
        -- Disjunctions on the left can always be decomposed.
        cases h27
        case inl h28 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h29 : p2 := by
            -- One of the premise coincides with the conclusion.
            exact h3
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h30 := h2 h29
          -- False on the left can always be used.
          apply False.elim h30
        case inr h31 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h32 : p2 := by
            -- One of the premise coincides with the conclusion.
            exact h31
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h33 := h2 h32
          -- False on the left can always be used.
          apply False.elim h33
  case inr h34 =>
    -- Disjunctions on the left can always be decomposed.
    cases h34
    case inl h35 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h36 =>
        -- Conjunctions on the left can always be decomposed.
        let h37 := h36.left
        let h38 := h36.right
        -- False on the left can always be used.
        apply False.elim h38
      case inr h39 =>
        -- Disjunctions on the left can always be decomposed.
        cases h39
        case inl h40 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h41 : p2 := by
            -- One of the premise coincides with the conclusion.
            exact h3
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h42 := h2 h41
          -- False on the left can always be used.
          apply False.elim h42
        case inr h43 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h44 : p2 := by
            -- One of the premise coincides with the conclusion.
            exact h43
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h45 := h2 h44
          -- False on the left can always be used.
          apply False.elim h45
    case inr h46 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h47 =>
        -- Conjunctions on the left can always be decomposed.
        let h48 := h47.left
        let h49 := h47.right
        -- False on the left can always be used.
        apply False.elim h49
      case inr h50 =>
        -- Disjunctions on the left can always be decomposed.
        cases h50
        case inl h51 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h52 : p2 := by
            -- One of the premise coincides with the conclusion.
            exact h3
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h53 := h2 h52
          -- False on the left can always be used.
          apply False.elim h53
        case inr h54 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h55 : p2 := by
            -- One of the premise coincides with the conclusion.
            exact h54
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h56 := h2 h55
          -- False on the left can always be used.
          apply False.elim h56



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41348939799675218677662783378 : ((((p4 ∧ (((True ∨ False) ∨ ((((p1 ∧ False) → True) ∧ p2) → p3)) ∨ (p1 → p4))) ∨ (((p2 ∨ p4) ∧ p1) ∧ (p2 ∨ True))) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_383393924090563600401897144652 : (((((p4 → ((False ∨ (((((True → (((p2 ∨ (False → (p1 ∨ p1))) ∧ p3) → p2)) ∧ p2) → True) → p3) ∧ p2)) ∧ True)) ∨ p1) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_242804357816294660157554063015 : ((p3 → p3) ∧ ((p3 ∧ (((True → ((((p1 ∧ False) → p4) ∧ (p2 → p1)) ∨ p3)) ∧ (((False ∨ p3) ∨ p2) ∧ p4)) ∨ p1)) ∨ (p2 ∨ True))) := by
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
theorem thm_5_vars_59275284388177037134096891546 : (((p3 ∨ p1) ∨ (p1 ∧ (p5 ∨ ((p4 ∨ True) ∨ ((((p5 → p4) ∧ True) ∨ p4) → ((((False ∧ (p2 → True)) → True) ∨ False) ∨ p2)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_786767279652930481547320741097 : (((p4 ∨ ((((p1 → False) → p2) → p1) ∨ (p2 → ((False ∧ False) ∨ ((p2 → ((p2 ∨ ((False ∧ (p1 → p3)) ∧ p2)) ∨ p4)) ∨ True))))) ∨ p2) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609180167279290896062049467212 : (((((((p5 → (p3 → False)) → False) → ((((p4 ∨ False) → True) → p3) ∨ (False ∧ ((p3 ∧ p5) ∨ (False ∧ (p3 ∨ p5)))))) ∨ False) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190062118547388491922942415730 : (((((p5 → ((p1 ∧ False) → p2)) ∨ p2) → p4) ∧ p5) ∨ ((p4 ∧ ((True ∨ ((True ∨ (p3 ∧ (p5 → True))) ∨ p3)) ∧ p1)) ∨ (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2284640649063149886541820036 : (((p2 → (p3 ∨ (p3 ∧ p3))) ∧ ((False ∧ p2) ∨ (True ∧ (p5 ∧ True)))) ∨ (((True → (True ∨ (p3 ∨ (p2 ∨ p1)))) ∧ True) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185310197687235595394233198217 : ((p3 ∧ ((((p5 → p4) ∧ True) ∧ ((p2 ∨ True) ∧ p3)) ∨ p3)) ∨ (((((p2 ∧ ((True → p4) ∧ False)) ∧ False) → p3) ∧ p3) ∨ (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38893857281936980626695452473 : (((((False ∨ p1) → p4) ∨ (((p5 ∨ ((p5 ∨ (p3 ∧ (p4 ∨ p2))) ∧ p3)) ∧ ((True → (p1 ∨ (True ∧ p4))) ∧ p5)) ∨ p1)) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721426295558914786010329131434 : ((((p1 ∧ ((p2 ∨ True) ∨ p5)) → (((p5 → (p5 ∨ ((False ∨ (p3 → p5)) → p4))) → ((p5 → (p3 ∨ p5)) ∧ (p3 → p2))) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52006386072127411213625427823 : (((p2 ∧ ((True → (((p1 ∧ p2) ∨ False) ∧ p2)) ∨ (((p2 → p2) → False) → p4))) ∨ ((p1 ∨ p2) → (True ∨ (p3 ∧ (p5 ∧ p1))))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656285377435007022182014163307 : (((((False ∨ (p1 → (((((p1 → p3) ∧ p3) ∨ p3) ∨ p4) ∨ p5))) ∧ (p2 ∧ ((p4 → False) → ((True → p4) ∧ True)))) ∨ (p4 ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659084222204986571884899558900 : ((((p2 → ((((True → p1) ∨ p5) ∧ p5) → (p1 → (p4 ∧ (p2 ∧ ((((p5 → (p3 → p3)) → p3) ∧ p2) ∧ p5)))))) ∨ (p1 ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198713952528129967181761759915 : ((p5 ∨ ((p5 → (p3 ∧ (p5 ∧ p3))) → p5)) ∨ (((p5 ∧ ((((p1 ∨ p5) ∧ (p1 ∧ True)) ∨ p1) ∧ p5)) → p1) ∨ ((p5 → p3) ∨ p5))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h8.left
      let h14 := h8.right
      -- One of the premise coincides with the conclusion.
      exact h13
  case inr h15 =>
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168256447440276575155692316486 : (((False ∨ (p5 → p5)) → (p5 ∧ ((((p2 → ((False ∨ True) → p3)) ∨ p2) ∨ p2) ∧ True))) → (p5 ∨ (((False ∧ p2) → p5) → (False ∧ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False ∨ (p5 → p5)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315910669357240846649326533055 : (p3 ∨ (True ∧ (((p5 → p1) → False) ∨ ((((p4 → (((p3 ∨ True) → (p3 ∧ p4)) ∨ ((False → p2) ∨ p3))) → p3) ∧ (p4 ∧ True)) → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : (p4 → (((p3 ∨ True) → (p3 ∧ p4)) ∨ ((False → p2) ∨ p3))) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h8
    -- False on the left can always be used.
    apply False.elim h8
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h6
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217577994347081058737868146893 : ((((p1 ∨ p4) ∨ True) → False) → ((p4 ∧ (True ∧ (p3 ∨ (p5 ∧ (((False → True) → (False ∨ p5)) ∧ True))))) ∨ (p3 ∨ (True ∧ (False ∨ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p1 ∨ p4) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49451826768905801058800119622 : (((((p4 ∨ p1) ∨ ((p1 → (((p2 → (False → p3)) ∨ (p5 ∨ False)) → p4)) ∨ (True ∨ (p5 ∧ p5)))) ∨ p5) → ((p2 → False) ∨ True)) ∨ False) := by
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
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h10 =>
          -- Conjunctions on the left can always be decomposed.
          let h11 := h10.left
          let h12 := h10.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_564750040322168025503642854957 : (((True → (((p3 ∧ (((p5 ∧ False) ∧ (((p1 ∨ ((False ∨ False) → p4)) → (p3 → p2)) ∨ (p2 ∨ (p5 → p1)))) ∧ p4)) ∧ p5) ∨ True)) ∧ True) ∧ True) := by
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
theorem thm_5_vars_775750139672978579479740096041 : (((False ∨ (p3 ∨ (p4 → ((((p1 → (p3 ∧ p4)) ∨ (False ∨ p2)) → (False ∨ p2)) ∧ (((p3 ∧ ((p2 → p2) ∧ False)) ∧ p3) → p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174187370493437762422948337883 : (((p2 → ((False ∨ (p3 ∧ (p5 → p3))) ∧ ((p1 ∨ p1) ∨ False))) ∨ (p2 ∨ p1)) → ((((p4 ∧ p2) ∧ (p1 ∨ p4)) ∧ False) ∨ (True → True))) := by
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
theorem thm_5_vars_208583070979899261789162041792 : (((False → p5) → ((p2 ∧ p1) → p2)) → ((((True → (True ∧ p2)) ∧ p5) ∨ (p2 → p2)) ∨ ((p3 ∧ True) → ((p3 → p4) → (p4 → True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261195493852504476515900203659 : ((p4 → p5) → ((True ∧ (((((True ∧ (p2 ∨ (False ∧ (p5 ∨ False)))) ∨ (True ∧ True)) ∨ p2) ∨ p1) ∧ ((False → (p3 ∨ p2)) ∧ p2))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68090533788800235588774498678 : ((p2 → (p5 ∨ ((True → (False ∧ p2)) → (((((p3 ∧ True) ∨ p4) ∧ p3) ∧ (p5 ∨ (p1 ∧ p2))) ∨ (True → (p3 ∨ (p5 → p1))))))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_675777243736551584862030675865 : (((((((p2 ∨ (((False ∧ True) ∨ ((p2 ∧ p1) ∧ p2)) ∨ True)) ∨ True) ∨ p3) → ((True ∧ True) → False)) ∧ (p2 ∧ ((False ∨ p2) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164578349491763263789534856102 : (((((p4 ∧ p5) → p2) → (p1 → ((p1 ∨ ((p5 ∨ p3) ∧ (True → p3))) → p3))) ∧ p1) ∨ ((True ∨ (p3 ∨ (True ∧ p5))) ∨ (p1 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_743543542337825531885937918039 : ((((True ∧ True) → ((True ∧ ((True ∧ ((((p1 → ((p4 ∨ False) ∧ ((p2 ∨ p5) ∧ p2))) ∧ p3) → p5) → p4)) → (p5 ∨ False))) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65122417599733023452780620259 : ((p2 ∨ (True → (p5 → (p1 ∧ (p4 → ((p1 ∨ False) → ((p2 ∨ (((p3 → False) ∧ p4) ∨ p5)) → (p2 → (p3 ∨ (p3 ∨ p1)))))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116600913658363192210415996264 : (((p5 ∨ p4) ∧ (((((p5 → p4) ∧ p2) → p3) ∧ (True ∨ p1)) ∧ (p2 → (((True → (p5 → p2)) → (False ∨ True)) ∧ p4)))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111615732268724706047099270966 : (((((((True → ((p5 → (True → p1)) → ((((False ∧ p1) ∨ p4) ∧ False) ∧ p4))) ∧ (p1 → p3)) → True) → p3) ∨ p4) ∨ p1) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_389790062231996825915848567319 : ((((((p5 ∧ (p1 ∧ False)) ∨ (p1 ∨ (False ∧ (True ∧ (p5 ∨ True))))) ∨ (p2 → ((p5 ∨ (True → p3)) ∨ ((p3 ∨ True) ∧ p1)))) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_112423698986957161643622746719 : ((((p3 → ((p2 → (p5 → True)) ∧ ((p1 ∨ (p4 ∨ (p4 ∨ (False ∨ (p1 → ((p3 ∧ p3) ∧ p2)))))) → p1))) ∧ p1) → p3) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612816211589376670181438482665 : ((((((p1 ∧ p3) → (p1 → (p1 ∧ ((((p3 ∧ (p1 ∧ p2)) ∨ p2) ∧ True) ∨ ((p4 ∧ (p5 ∧ True)) ∧ p5))))) ∨ (p2 → p2)) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55971760444833226902002655785 : (((((p5 → p2) ∨ True) ∧ p4) ∨ (p5 ∨ (((p3 ∨ (p5 → False)) → (p5 ∨ (p2 ∨ p5))) ∧ (((p3 → (p2 ∨ p1)) → p5) ∨ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323725188170613571369877066782 : (p5 ∨ (((True ∨ p2) → ((False ∨ (((p2 ∧ (p5 → (True ∧ p2))) → p1) ∧ ((p3 ∨ p2) ∧ False))) ∧ p1)) → (((p1 ∧ p4) ∧ p2) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- False on the left can always be used.
      apply False.elim h10
    case inr h12 =>
      -- False on the left can always be used.
      apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_384798291093113196936820911973 : ((((((True ∨ True) → (((p5 ∧ False) → (True ∧ (p2 → (True ∨ (False ∧ p5))))) ∧ (((p4 ∧ p2) ∧ (p1 ∧ False)) ∧ p4))) → p1) ∨ p4) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ True) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- One of the premise coincides with the conclusion.
  exact h7
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731067558456705447933570032446 : ((((p1 ∨ (True ∨ p4)) → (((p5 ∧ p2) ∨ (((True ∨ p3) ∧ ((p3 → True) ∨ (p1 → p4))) → (True ∨ (p3 ∧ p3)))) ∨ (p4 ∧ p3))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h11 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h17 =>
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h18 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h19 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h20 =>
        -- Disjunctions on the left can always be decomposed.
        cases h16
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h24
      -- Conjunctions on the left can always be decomposed.
      let h25 := h24.left
      let h26 := h24.right
      -- Disjunctions on the left can always be decomposed.
      cases h25
      case inl h27 =>
        -- Disjunctions on the left can always be decomposed.
        cases h26
        case inl h28 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h29 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h30 =>
        -- Disjunctions on the left can always be decomposed.
        cases h26
        case inl h31 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h32 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43113077522949152680989065822 : ((((((((False → p2) → (p4 ∧ False)) → ((p3 ∧ True) ∧ p4)) ∨ ((p1 → False) ∧ p5)) ∨ (False → (p4 → (p2 → p2)))) ∧ p1) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225090247207775632357811199393 : (((p2 ∧ True) ∧ False) ∨ (p3 ∨ ((((False ∧ p1) → p4) ∧ p4) → (False ∨ (p5 → (p1 ∨ ((p5 → (p2 ∧ (p2 → p5))) ∨ (True ∨ False)))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150012546106595152232928586369 : ((p5 ∨ ((((p5 ∧ (((p2 ∧ p5) → ((p5 ∨ p4) ∧ True)) ∨ p1)) → p3) ∧ (p1 ∨ True)) ∧ (p4 → p4))) ∨ (((p3 ∨ p2) ∨ True) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44898477406648877857227913552 : ((((p3 ∧ (p4 → p5)) → (True → ((((((p2 → False) ∧ (p1 ∨ p1)) → True) → False) ∧ ((p3 ∧ False) ∨ p5)) → (True → False)))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59257924871845326676534288153 : (((p2 ∨ p5) ∨ ((p2 ∧ p1) ∨ (p5 ∧ (((((p1 ∨ ((True → (p3 ∨ (p3 → p2))) ∨ p1)) → p2) ∧ p1) ∨ True) → (False → True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340740432879451837647243305578 : (p2 → ((((((True → (((p2 ∨ p3) ∧ False) → (p3 ∨ p4))) ∧ p4) ∧ (((p5 ∨ True) ∧ p1) ∧ (p5 → p2))) ∨ (False ∧ p3)) ∨ False) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_740439866684052935889591265170 : ((((p1 ∨ p4) ∨ (((p4 ∧ (((True ∨ p2) ∧ (p5 ∧ p1)) ∨ (((False → p1) ∧ ((p1 ∧ p2) ∨ False)) ∨ p5))) ∨ p5) ∨ (False ∨ True))) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_230912329083858415582015606616 : (((p2 ∧ p5) ∨ p3) → ((((p4 ∧ True) ∨ (p2 ∧ True)) ∨ True) → (p3 ∨ ((p1 ∨ p5) ∨ (((p4 ∨ True) ∨ ((False ∨ p1) → p2)) ∧ p2))))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h10
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h16
      case inr h17 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h17
  case inr h18 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h19.left
      let h21 := h19.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h21
    case inr h22 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347660030731555466746253267899 : (p3 → (((False ∧ p4) → (p1 → p3)) → ((((((p1 → False) → p4) ∧ p2) ∧ p4) ∧ ((True ∨ (p5 ∨ (True ∧ p5))) ∨ False)) ∨ (p3 → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180502355094571223543099459852 : ((((p5 → True) → (((p4 → p2) ∧ p1) ∨ True)) ∧ (p3 ∧ (p3 ∨ p4))) → (((p5 ∧ (p2 ∧ (((p3 ∧ p2) → p5) ∧ p5))) ∨ p3) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51947869357189898225531667180 : ((((((p2 → (False ∨ p3)) → p5) → False) ∨ (((p1 → p4) ∨ (p4 ∨ p2)) ∨ p5)) ∨ ((((p5 ∧ False) → (True ∨ p2)) ∨ p1) ∨ p5)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_339969677914804066584195125294 : (p1 → (p1 → ((p1 ∧ (p3 → (p5 ∨ (p5 ∨ (p4 ∨ ((p4 ∧ p1) → ((False ∧ False) ∨ (((p5 ∧ p1) ∨ (p1 ∧ p1)) ∨ True)))))))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51905777611345883329843252513 : (((((p4 ∧ p1) ∧ (p2 → (p1 ∨ (False ∨ (p3 ∨ (False → True)))))) ∧ (p5 ∧ p3)) ∨ (((False ∨ p2) → (p3 ∧ p3)) ∨ (True ∨ p1))) ∨ p5) := by
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
theorem thm_5_vars_300774681012648805871297039277 : (False ∨ (((p4 ∨ ((((p4 ∧ (True ∧ (p4 ∨ (p1 ∨ p3)))) ∧ p3) ∧ p3) ∨ p3)) ∨ p1) ∨ (True ∨ ((p2 → p1) ∨ ((False ∨ p1) ∧ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313121482964407882944771834774 : (p3 ∨ ((((True ∨ (((((p3 ∧ p5) → (p2 → (p4 → True))) ∧ p3) ∨ p1) ∧ p2)) ∧ (p1 ∨ p1)) ∧ ((p4 ∧ (False ∨ p3)) ∨ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111656869101943261840821567209 : ((((False ∧ (p2 ∨ ((((p5 ∧ p2) ∧ True) ∨ (p2 ∨ p1)) → (((False ∨ p5) ∨ ((p4 ∧ p5) ∧ p4)) ∧ p1)))) ∨ True) ∨ p5) ∨ (p2 ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2373190348163081797839124459 : (((p5 ∧ ((p4 ∨ p5) ∧ p5)) ∨ (p4 ∨ ((False → p1) ∧ p3))) ∨ ((p3 ∧ (p3 → ((p2 ∧ (p5 ∧ False)) → p3))) → (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62367133749654591586358123144 : ((p3 ∧ ((p4 → ((p3 → (p5 ∨ (p3 ∨ ((True ∧ True) → p5)))) ∨ (p3 ∨ (True → True)))) ∧ ((((p3 → p5) ∧ p1) ∨ False) ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315866787691924432526304205958 : (p3 ∨ ((p4 → p5) → ((p2 → (((p1 ∧ p1) → p4) ∧ ((p5 ∨ ((p1 → (p5 → False)) ∨ p2)) → p5))) ∨ (((p5 ∨ p4) → p5) ∨ p3)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h5 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h6 := h1 h5
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_956468359993071662244360634607 : (((((p4 ∧ False) → p3) → (((p5 → (p4 ∨ False)) → ((False ∨ ((p1 ∧ False) ∨ p4)) ∨ ((p2 ∨ (p3 → (p3 ∨ p2))) ∧ p4))) ∧ False)) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p4 ∧ False) → p3) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612177447819593420398927439118 : (((((((((p5 ∨ p4) ∧ (False ∨ p5)) → p4) → p4) ∨ (((True ∨ p1) ∧ p1) → (p1 ∨ ((p2 ∧ p1) → p1)))) ∧ (p1 ∧ p2)) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302059201541750607451592641881 : (False ∨ (True ∧ (True → ((p2 ∨ (True → ((p4 → True) → (((p2 ∧ (True ∨ p4)) ∧ p5) ∧ p5)))) ∨ (False → (((p1 → p4) → p4) → p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_341708764185149284153950863759 : (p2 → ((((p1 → (p4 ∨ ((p5 ∧ p1) → (p2 ∧ (p4 ∨ (p1 → p5)))))) → p1) ∧ (((p3 → True) → p3) → (p3 ∨ p1))) ∨ (p1 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118298535464581150016329933445 : ((p1 ∨ (p3 ∧ (True ∧ ((((p2 → (False ∨ p4)) ∧ (((((False → p4) → (p1 ∧ p3)) ∧ True) ∨ p2) ∨ p5)) ∧ False) ∨ True)))) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136553887004126072079199705624 : ((((p3 ∧ False) ∨ p4) ∨ (((((p4 ∨ (p4 ∨ p4)) ∨ (p1 ∧ p1)) → (p3 ∧ p4)) ∨ ((p3 → p3) → p3)) ∧ p4)) ∨ (p1 → (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121861895829422554025333787462 : ((((p3 ∨ p4) → ((((p3 → True) ∨ (p2 ∨ p3)) → p3) ∨ ((p5 → (p3 → p3)) ∧ (((p4 → p4) ∧ False) ∨ True)))) → False) → (p2 ∧ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p3 ∨ p4) → ((((p3 → True) ∨ (p2 ∨ p3)) → p3) ∨ ((p5 → (p3 → p3)) ∧ (((p4 → p4) ∧ False) ∨ True)))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h5
      -- Implications on the right can always be decomposed.
      intro h6
      -- One of the premise coincides with the conclusion.
      exact h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h8
      -- Implications on the right can always be decomposed.
      intro h9
      -- One of the premise coincides with the conclusion.
      exact h9
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h2
  -- False on the left can always be used.
  apply False.elim h10
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h11 : ((p3 ∨ p4) → ((((p3 → True) ∨ (p2 ∨ p3)) → p3) ∨ ((p5 → (p3 → p3)) ∧ (((p4 → p4) ∧ False) ∨ True)))) := by
    -- Implications on the right can always be decomposed.
    intro h12
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h14
      -- Implications on the right can always be decomposed.
      intro h15
      -- One of the premise coincides with the conclusion.
      exact h15
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h17
      -- Implications on the right can always be decomposed.
      intro h18
      -- One of the premise coincides with the conclusion.
      exact h18
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h19 := h1 h11
  -- False on the left can always be used.
  apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789994559762058740070078182477 : (((p5 ∨ ((p3 → p3) ∧ (p3 ∧ (p5 ∧ (((((False → (p3 ∧ p1)) ∧ p3) → p3) ∧ p5) ∧ ((p5 ∨ False) ∨ (p4 ∨ (p2 ∨ True)))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_806312531526982952739660639456 : (((p4 → ((((p5 ∨ p2) → p3) → (False ∧ (p5 ∧ (p2 ∨ (False → (((((p1 → p3) ∧ p4) ∨ False) → (p2 ∨ p5)) → False)))))) ∨ True)) ∨ p5) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262207411384625673190974804978 : (True ∧ (((p5 ∧ (p4 ∨ ((True ∧ ((p5 → (p5 ∨ p2)) ∨ ((False → (p2 ∧ (p5 → (p5 ∧ p2)))) ∧ (p2 ∧ True)))) ∧ p5))) → p4) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356262219883975843875083735210 : (p5 → ((((p3 ∨ (p5 ∨ p4)) ∧ p1) ∧ ((p3 → p1) ∨ (p3 → ((False ∨ p5) ∧ p4)))) ∨ ((((p2 ∧ p4) → p5) ∨ p4) ∨ (False ∧ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670242070494501902182498366521 : (((((p3 ∨ ((p3 → p5) ∨ p4)) ∨ (p5 ∨ (True → (((p1 → p5) ∨ (p1 ∨ (p1 ∧ True))) ∨ (p1 ∨ p2))))) ∨ (True → (False → p3))) ∨ False) ∧ True) := by
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
theorem thm_5_vars_19642676553341644770733234301 : (((p1 ∧ (p1 ∧ (((p3 ∨ p5) → (p1 ∨ (True → (False ∨ True)))) → (p4 → p5)))) ∨ (p3 → ((p2 ∧ True) → (True ∧ (p3 ∨ p4))))) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707839341806077989905751414060 : ((((p2 ∧ ((p4 ∨ ((p3 → p5) → p4)) ∧ True)) ∨ ((p2 ∧ (p2 ∧ ((p3 → ((True → p4) ∨ (p4 → p5))) → (p4 → p5)))) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353410352786674593354508886913 : (p4 → (p1 ∨ (((False ∧ ((p2 ∨ ((True ∨ p5) ∧ p5)) ∨ ((False ∧ ((((p4 ∧ p5) ∧ p5) ∧ p2) ∧ p4)) ∧ (p4 ∧ False)))) ∨ p4) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40517256784961516074846139924 : ((((p4 ∧ (p5 ∨ ((((p3 → ((True ∨ False) ∨ p4)) ∨ (p5 ∨ (((p1 → False) ∧ p3) ∧ p3))) ∧ True) → (p3 ∧ False)))) ∨ p1) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609325177589301588778275644144 : ((((((p3 → p3) ∧ ((((p4 ∧ p5) → (False ∨ p2)) ∧ (p5 ∨ p2)) → ((((p5 ∧ (p3 ∧ p2)) ∧ True) ∧ p5) ∨ True))) ∨ p4) ∨ p5) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
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
theorem thm_5_vars_114966542513820984214082824774 : (((p1 → (True → (((((p1 ∧ p4) → False) → p3) ∧ p4) ∧ (p5 ∨ p3)))) → (((p3 ∨ p3) ∨ ((True ∨ True) → p2)) ∧ p5)) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_810803904486879017508488528701 : (((p5 → ((p4 ∨ p5) ∧ (p4 ∨ (True ∧ ((((False ∧ ((p1 ∧ p5) → (p4 ∧ (False ∧ p2)))) ∨ p2) ∨ (p2 → (True ∨ p2))) ∨ True))))) ∨ p4) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186435605949047106007238546279 : (((p2 → (p2 ∨ ((p2 ∨ ((p4 ∨ True) ∨ p2)) ∧ p3))) → False) → (((p1 → p3) ∧ (p3 ∧ ((p2 ∨ (p2 → (p4 → p1))) → False))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303760547019116918710485007915 : (p1 ∨ (((((p2 → (True ∨ p1)) ∧ (p4 ∨ (True ∨ ((((p3 ∨ p2) → True) → p2) ∧ p5)))) → ((p3 → p2) ∨ (p3 ∧ p1))) ∨ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148018771271040845100693249230 : ((((True → (p1 ∧ (p5 ∧ ((p2 → p2) → (p2 ∨ p4))))) → ((p3 → (p2 ∧ True)) ∨ p4)) ∨ (True ∨ True)) ∨ ((False ∨ p2) → (p5 ∨ True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46415659244582086795012856753 : ((((False → (True ∧ (True ∨ (p1 → (p4 ∨ p5))))) → (p4 ∧ ((p5 ∧ (False → ((p4 ∧ True) → True))) ∨ (p5 ∧ p4)))) ∧ (p3 ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



