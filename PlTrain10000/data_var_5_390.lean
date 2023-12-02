variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_645431426555856526148546495470 : ((((p4 ∨ (((True → (p1 → ((p5 ∨ p1) ∧ True))) → (p3 ∧ p5)) ∧ ((p5 ∧ True) → (((p1 ∧ True) ∨ p1) ∨ (p4 → True))))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_765228788294550243535551861545 : (((p4 ∧ ((((True ∧ p1) ∨ p3) ∧ (((p5 ∨ (p5 → (((True ∨ True) → p3) ∨ (p4 ∧ p2)))) → (False → p3)) ∨ p1)) → (True → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112092059306414324873079710768 : ((((p2 → p1) ∨ (False ∨ ((((p2 → (p3 → ((False ∨ p3) → (True → p3)))) ∧ p4) ∨ (p4 ∨ (p4 ∨ False))) → False))) ∨ p1) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217105921733611741261268709739 : ((((True ∨ False) ∨ p2) ∨ p4) → (((p1 ∧ (p2 → p4)) ∨ p4) → ((((False ∧ False) → p5) → ((((p5 ∧ True) ∨ True) ∨ p2) ∨ True)) ∨ True))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h9 =>
          -- False on the left can always be used.
          apply False.elim h9
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h16 =>
          -- False on the left can always be used.
          apply False.elim h16
      case inr h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_723148957422555171095904455041 : (((((True → False) ∨ p1) ∧ (((((True ∨ ((True → p3) → (p1 → p2))) → p3) ∧ True) ∨ (False ∨ ((True ∨ (p2 → True)) ∨ p3))) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60954653190039522459529337816 : ((False ∧ (((p3 ∧ ((p3 → (((((p3 ∧ p5) ∨ p3) ∨ p5) ∨ (p5 ∨ (p4 → (p1 ∨ False)))) ∧ (p2 → False))) → True)) → p5) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698068086317320975214873301471 : ((((((True → p1) ∧ ((p5 ∨ ((p5 ∨ p1) ∧ p2)) ∨ False)) ∨ p2) ∨ ((((p1 ∨ (p2 → False)) ∧ p3) ∧ p4) ∨ ((p1 → p5) ∨ True))) ∨ False) ∧ True) := by
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
theorem thm_5_vars_504228082035500544157917896226 : ((((p4 ∧ (True ∨ p1)) → (((((p3 ∨ True) ∧ True) ∧ (((p1 ∧ (p2 ∧ p1)) ∧ (p2 ∨ p3)) ∧ p5)) ∨ (p3 ∨ p4)) → (False ∨ True))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    cases h6
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h5.left
      let h10 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h9.left
      let h12 := h9.right
      -- Conjunctions on the left can always be decomposed.
      let h13 := h11.left
      let h14 := h11.right
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h1.left
        let h19 := h1.right
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h21 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h22 =>
        -- Conjunctions on the left can always be decomposed.
        let h23 := h1.left
        let h24 := h1.right
        -- Disjunctions on the left can always be decomposed.
        cases h24
        case inl h25 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h26 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h27 =>
      -- Conjunctions on the left can always be decomposed.
      let h28 := h5.left
      let h29 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h30 := h28.left
      let h31 := h28.right
      -- Conjunctions on the left can always be decomposed.
      let h32 := h30.left
      let h33 := h30.right
      -- Conjunctions on the left can always be decomposed.
      let h34 := h33.left
      let h35 := h33.right
      -- Disjunctions on the left can always be decomposed.
      cases h31
      case inl h36 =>
        -- Conjunctions on the left can always be decomposed.
        let h37 := h1.left
        let h38 := h1.right
        -- Disjunctions on the left can always be decomposed.
        cases h38
        case inl h39 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h40 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h41 =>
        -- Conjunctions on the left can always be decomposed.
        let h42 := h1.left
        let h43 := h1.right
        -- Disjunctions on the left can always be decomposed.
        cases h43
        case inl h44 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h45 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
  case inr h46 =>
    -- Disjunctions on the left can always be decomposed.
    cases h46
    case inl h47 =>
      -- Conjunctions on the left can always be decomposed.
      let h48 := h1.left
      let h49 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h49
      case inl h50 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h51 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h52 =>
      -- Conjunctions on the left can always be decomposed.
      let h53 := h1.left
      let h54 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h54
      case inl h55 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h56 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624974954994196510415802341069 : ((((p5 ∨ (p1 ∨ ((p5 ∨ (p3 ∧ p4)) ∨ (p3 ∨ (((p3 ∧ (p3 → True)) → p2) ∨ (p3 ∧ (True ∧ ((p1 → p2) ∨ False)))))))) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_717645319374902323655576850195 : ((((p5 → (False ∧ (p5 ∨ p4))) ∧ ((p3 ∧ p2) ∨ (True → (p4 ∨ (((((p1 → False) → (p3 ∧ p2)) ∧ (p5 ∨ True)) ∨ p1) ∧ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677874976380908180915635166404 : ((((((((p4 ∧ ((p5 ∧ True) ∧ p1)) ∨ (True ∧ ((p3 → p5) → p4))) ∨ p1) → p4) ∨ (p2 ∨ p1)) ∨ (False ∨ ((False ∨ p1) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353531180848026201538189872865 : (p4 → (p3 ∨ ((((p1 → (True → (p3 ∨ (True ∧ p1)))) ∧ (((p5 → (p2 → p3)) → ((p1 ∨ True) → (p2 ∨ p4))) → p5)) ∧ p2) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309908234491643468072730280074 : (p2 ∨ ((((p4 ∧ (True → (((p3 ∧ False) ∧ (False ∨ p3)) ∨ (p4 ∧ (False ∧ p5))))) ∨ True) ∧ p5) ∨ ((p2 → ((p4 → p3) → p2)) ∨ p5))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_790271662554726067264843824152 : (((p5 ∨ (p1 ∧ (p5 ∨ (p3 ∧ ((True ∧ (False ∧ (p3 → (((False → (False ∧ (False ∧ (p4 ∧ True)))) ∧ True) ∨ (p4 ∧ p3))))) ∨ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303991719050892112038140639122 : (p1 ∨ (((p3 ∧ p5) ∨ (((((False ∧ p2) ∧ (p1 ∧ p4)) ∧ ((((p4 → p2) → p3) ∧ p5) → p3)) ∨ p5) ∨ (p4 → (p4 ∨ p2)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670277184845647067279677920337 : (((((False ∨ ((p2 → p2) → p5)) → ((True ∨ p2) ∧ (False ∨ ((p2 ∨ (p1 ∧ p5)) → ((p3 ∨ p1) ∧ p1))))) ∨ (p5 → (p5 ∨ p5))) ∨ p4) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225309396159633330590468859719 : (((False ∨ p3) ∧ False) ∨ ((p5 ∨ p3) ∨ ((((p5 → (p5 → True)) ∨ (((p4 ∨ p3) ∨ ((True ∨ p4) ∨ (p1 → True))) → True)) ∨ True) ∨ p2))) := by
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
theorem thm_5_vars_643429454156152675232934425916 : ((((p4 ∧ (((p2 ∧ ((((((p4 → True) ∨ p5) → True) → p2) → (p2 ∧ p3)) ∨ p1)) ∧ (p5 ∧ (p2 ∨ (p5 → False)))) → p4)) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258168376460125473945925347700 : ((p4 ∨ p4) → ((((p2 ∨ (True ∧ (((False ∧ (p5 ∨ p4)) ∨ ((True ∧ p3) → p5)) ∧ True))) ∨ False) → (p1 ∨ (p3 → p2))) ∨ (p4 ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355531576093314549337392074139 : (p5 → ((((p3 ∨ (((p1 → p5) ∧ p2) → (p5 ∨ p4))) ∧ ((p3 ∧ ((p2 → (True ∨ p4)) ∧ p4)) ∨ (p1 ∧ p2))) ∧ p5) ∨ (True → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41924663844483689779862914034 : ((((p5 ∧ (p2 → False)) → (True ∧ (p5 ∧ ((((p3 ∨ p3) ∨ (((p5 ∧ p2) ∨ p1) → (p2 ∨ True))) ∧ (p4 ∨ p1)) ∨ True)))) ∨ p3) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199855387457742752989284493154 : (((False ∨ ((p1 → True) ∨ p4)) ∧ (p1 ∨ p1)) → ((p5 ∧ p2) ∨ ((((p2 ∨ p2) ∧ (p3 ∨ ((True ∨ p2) → (p5 → p1)))) ∨ p5) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h8
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h10
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
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
theorem thm_5_vars_134280774349702374797964331774 : ((((False ∧ False) ∨ (True → (((p4 ∧ p2) → ((p5 → p1) → (True ∧ (p3 ∧ False)))) → (False ∧ (False ∧ p1))))) ∨ True) ∨ ((p2 ∨ p4) ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64463165804513571094142908534 : ((p1 ∨ ((p3 → (p3 → (p4 ∨ (p5 ∧ ((p3 ∧ ((((p5 ∧ p1) ∨ p4) → p1) → (False → p2))) → p3))))) ∧ (p1 → (p1 → p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133816045830064692405157829580 : ((((p4 → False) ∧ ((p4 ∨ ((p2 ∨ (p4 → (((p3 → p4) → p5) ∧ p3))) ∧ ((p4 ∨ p4) → p5))) → p1)) ∧ p3) ∨ (True ∨ (p4 ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44608720524917670407636888363 : ((((p1 ∧ (p3 ∨ ((p5 → (p5 ∧ p1)) → False))) → ((((p2 ∧ p3) → p2) → ((p4 → (p2 ∨ p1)) → (p5 → p1))) ∨ p4)) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68887868182133757237586018095 : ((p4 → (p3 ∧ (((p4 → ((p5 ∨ (p2 → (p1 ∧ p3))) ∧ p1)) ∧ ((((False ∨ p3) → ((p1 ∧ p4) ∧ p4)) ∨ False) ∧ True)) → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_36869146523422682415926468489 : ((p5 → (((p4 ∨ p5) ∧ (p1 ∧ p4)) ∨ ((p2 ∨ (p3 → ((p2 ∧ True) ∧ p3))) ∨ ((p4 → (False ∧ (True ∨ p4))) → (p1 → p5))))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60548319004835833140106641672 : ((True ∧ ((False ∧ (((p4 ∨ ((p2 ∨ p1) ∨ (((True ∧ (p2 ∨ p2)) → False) → (((p4 ∨ False) → p3) ∧ p4)))) ∧ p4) → p5)) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309302982346932249519866640844 : (p2 ∨ ((((p3 ∨ False) ∨ (False ∨ ((((((p1 → ((p4 → True) ∧ p2)) → p2) → p1) ∨ (p5 ∨ p5)) → False) ∨ p5))) ∧ p5) ∨ (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197800953992922528368427565364 : ((((p5 ∧ True) ∨ p1) ∨ ((p4 ∨ p1) ∧ p5)) ∨ ((((p2 ∨ True) ∨ False) ∨ True) ∨ ((True → ((p5 ∧ (p3 ∨ (p5 ∧ True))) ∧ True)) ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705216217205597115390470124915 : ((((((False ∧ p4) → (p2 ∨ (p1 ∨ p2))) ∧ p5) ∧ ((p2 ∧ p1) ∨ (p4 → ((p4 ∧ (((p1 ∨ p5) → p1) ∧ False)) ∧ (p4 ∨ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_791864442086532882108415351516 : (((True → (((p5 ∧ True) → (p4 ∨ (((((False → p4) ∧ (p4 ∨ p5)) → ((p2 ∧ True) → p2)) → (p1 → p3)) → False))) ∧ (p2 ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67820944677913256309390577142 : ((p2 → ((p5 ∨ (((p3 ∨ p4) ∨ (((p4 ∧ p5) ∧ p1) ∧ ((p4 ∨ False) → True))) ∧ (p1 → ((True ∧ p1) ∨ (p3 ∨ p2))))) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1721431115071641995776749961 : (((((True → (p2 → p2)) → (p3 → False)) ∨ (p5 ∨ (p4 → p5))) ∨ (((p5 ∨ (True ∧ p2)) → p1) ∨ True)) ∧ (True ∨ (False ∨ False))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150849997658808443662626709267 : (((((p4 ∨ False) ∧ (((p4 ∨ False) → (p3 → p4)) ∨ p4)) ∧ ((True ∧ p4) ∧ (p2 ∨ (p2 ∧ False)))) ∨ True) → ((p1 ∨ (p2 → False)) ∨ True)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h4.left
        let h10 := h4.right
        -- Conjunctions on the left can always be decomposed.
        let h11 := h9.left
        let h12 := h9.right
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h14 =>
          -- Conjunctions on the left can always be decomposed.
          let h15 := h14.left
          let h16 := h14.right
          -- False on the left can always be used.
          apply False.elim h16
      case inr h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h4.left
        let h19 := h4.right
        -- Conjunctions on the left can always be decomposed.
        let h20 := h18.left
        let h21 := h18.right
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h22 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h23 =>
          -- Conjunctions on the left can always be decomposed.
          let h24 := h23.left
          let h25 := h23.right
          -- False on the left can always be used.
          apply False.elim h25
    case inr h26 =>
      -- False on the left can always be used.
      apply False.elim h26
  case inr h27 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349500950232291195752468587371 : (p3 → (p5 → (p2 ∨ (((False ∨ p4) ∨ ((p5 → (True ∧ ((True → ((p5 ∨ p1) → True)) ∧ ((p2 → False) ∧ p2)))) ∧ False)) ∨ (p5 → p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171536849916900378034837767223 : (((((p3 ∨ False) ∨ (((p2 ∨ (p1 ∨ False)) ∨ (True ∧ True)) ∧ p3)) ∨ True) ∨ p1) ∨ (((p1 → p5) → (False ∧ (p4 ∨ p4))) → (p1 ∧ False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251825163004696731815955285832 : ((p3 → p4) ∨ (p2 ∨ (True ∧ ((((p5 ∧ (((p5 ∧ (p2 → (p3 ∨ True))) ∨ (p4 ∧ (p5 → p3))) → p5)) ∨ (True ∧ True)) ∨ True) ∨ p2)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58071872828147095290627883041 : (((False ∧ p4) ∧ (p1 ∧ (((p3 ∧ ((p1 → p3) ∧ ((False ∨ True) ∧ p1))) ∧ (p5 → ((p5 ∨ (p3 → (p1 ∧ p1))) ∨ p3))) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112707388283764920253539581128 : (((((p4 → p1) ∨ ((True → p2) ∧ ((True ∨ p5) ∧ ((p4 → True) → (True ∧ p5))))) → (((p5 ∧ p2) ∧ True) ∨ p2)) → False) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150600231075546729454731833386 : ((((True ∨ False) → (((((False → p2) → (p4 ∨ p4)) ∧ False) ∧ (p1 ∧ (False ∧ (p4 ∨ p3)))) ∧ p3)) ∧ p2) → (((p5 → False) → True) → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : (True ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183923238876085706540475188522 : (((p2 ∧ (p2 ∨ ((((False ∨ p1) ∧ False) ∨ p4) ∧ p4))) ∧ p1) ∨ (((False ∧ (p3 ∧ p3)) ∨ (p5 → ((p1 ∨ (True ∧ p3)) ∨ p2))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148405095553523598613311316072 : ((((((((p1 ∧ True) → True) → ((p5 → p4) ∨ p2)) → p2) → p3) ∧ p2) → (((p4 ∨ False) → p4) ∧ p3)) ∨ (False ∨ ((False ∨ p3) ∨ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h1.left
    let h5 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h9 : ((((p1 ∧ True) → True) → ((p5 → p4) ∨ p2)) → p2) := by
    -- Implications on the right can always be decomposed.
    intro h10
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h11 := h7 h9
  -- One of the premise coincides with the conclusion.
  exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248058292791960997553108506031 : ((p1 ∨ p5) ∨ (False ∨ ((p5 → False) ∨ ((p4 → ((False → True) → (p2 ∧ (((p5 ∨ True) ∧ (False → p1)) ∨ ((p1 ∨ True) ∧ False))))) ∨ True)))) := by
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
theorem thm_5_vars_9385206403036995438658409806 : ((((((False ∨ True) ∧ False) ∧ p4) ∨ ((((p3 → ((((p3 ∧ p2) → p4) ∧ p3) ∧ (p1 ∨ p4))) → False) ∨ False) → (p3 ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65519527404496691419646103197 : ((p3 ∨ (p2 ∨ (((((((((True → (p4 ∧ (p4 ∧ (p1 ∨ (p3 → p5))))) ∨ False) ∧ p2) ∨ p1) → p2) ∨ p1) ∧ p2) → p1) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68754510024162726446329904361 : ((p4 → (((p5 ∨ (p3 ∨ (((((p5 → p4) ∧ True) → p5) ∨ True) ∧ p3))) ∧ p5) ∨ ((p3 ∧ ((p2 ∧ (p1 ∨ p2)) ∨ True)) ∨ p4))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233986504549254555674104864335 : ((p5 ∨ (True ∨ p1)) → (((False ∨ (((p5 ∨ False) → False) → p2)) → (p1 → (p4 ∨ False))) ∨ ((False → p5) ∨ ((p1 ∨ (True → p5)) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305714001626730202503346641871 : (p1 ∨ (((p1 ∧ p4) → ((p2 → ((p5 ∨ p1) ∨ False)) → p2)) → (p1 → ((True → (True → (False ∨ (p3 ∧ False)))) → (False ∧ (False ∧ p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- False on the left can always be used.
    apply False.elim h11
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h12 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h13 := h3 h12
  -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
  have h14 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h13, we can now drive its conclusion.
  let h15 := h13 h14
  -- Disjunctions on the left can always be decomposed.
  cases h15
  case inl h16 =>
    -- False on the left can always be used.
    apply False.elim h16
  case inr h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- False on the left can always be used.
    apply False.elim h19
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h20 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h21 := h3 h20
  -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
  have h22 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h21, we can now drive its conclusion.
  let h23 := h21 h22
  -- Disjunctions on the left can always be decomposed.
  cases h23
  case inl h24 =>
    -- False on the left can always be used.
    apply False.elim h24
  case inr h25 =>
    -- Conjunctions on the left can always be decomposed.
    let h26 := h25.left
    let h27 := h25.right
    -- False on the left can always be used.
    apply False.elim h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166401320258199043707459721738 : ((False ∨ (p3 ∨ ((p5 ∧ (((p1 → (p1 ∧ (True → p1))) ∧ p5) → (p4 → p2))) ∨ p4))) ∨ ((p4 ∨ (True ∨ (p1 ∧ False))) ∨ (p4 ∨ p2))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_640850273342648332806587550708 : (((((p3 → p3) ∧ (p3 ∨ (True → (p1 → ((p4 ∨ ((p2 ∨ False) ∧ ((((p3 → False) ∧ p3) ∧ p2) ∧ (p1 → True)))) → p5))))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171937034668291856179330126100 : ((((((True → (p4 → False)) → ((True ∧ p4) ∨ False)) → p1) → False) ∧ (p5 → True)) ∨ ((False ∨ (((p1 ∨ p5) ∨ (p2 → True)) → False)) → p3)) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : ((p1 ∨ p5) ∨ (p2 → True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h4
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_808107160110864889899706536055 : (((p4 → (p1 ∧ ((((p2 ∨ (p2 ∨ ((p5 ∨ p3) ∧ True))) ∧ p5) ∨ (p3 → (p5 ∧ (False ∨ True)))) ∨ ((p1 → p1) ∨ (p5 ∨ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346124771064102785735489474972 : (p3 → ((True → ((False → (p2 ∧ ((((p2 ∨ p2) ∨ (p3 ∧ p5)) ∨ (p4 ∧ p5)) ∧ (True → p2)))) ∧ (p5 ∧ (p1 → (p1 ∨ p3))))) → p5)) := by
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
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200437438883770785430324229712 : (((p4 ∨ p1) ∨ (((p3 ∧ p3) ∨ p3) → p3)) → (p2 → ((p1 ∨ ((True ∨ (p2 ∨ ((p5 → p2) ∧ p2))) → ((p2 → True) → p5))) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42693082963922872099706391486 : (((p5 ∨ ((p3 ∨ (((False ∧ (False → (p3 ∧ (False ∨ ((p5 → (p4 → p1)) ∧ True))))) ∧ True) → (p2 → (p2 ∨ p1)))) → p2)) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180246612842102714166858834975 : (((True ∨ ((True ∧ p4) → (((p1 ∨ p2) ∨ False) ∧ (p4 ∨ p4)))) → p1) → ((p3 → ((False ∨ (p5 → ((p4 ∧ True) ∨ False))) ∨ True)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115524773693413387484627376245 : ((((p4 ∧ p3) → (p4 ∨ (p3 ∨ (p4 ∧ p4)))) → ((((p2 ∨ p5) ∨ (((False ∧ p2) ∧ p2) ∨ p5)) → (p3 ∧ False)) ∨ False)) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_644048031215121903751964725107 : ((((True ∨ ((p1 ∨ ((False ∨ True) → ((False ∨ p3) ∨ ((True → True) ∨ p3)))) ∧ ((((p2 ∧ p3) → p4) → (True ∧ True)) ∨ p4))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256957523776450459851127990834 : ((p1 ∨ p5) → (((p5 → ((p3 ∨ p3) → (True ∧ (((p5 → (p1 ∧ (p3 → p4))) ∧ p5) → False)))) → (p2 → False)) ∨ (True → (p1 ∨ p5)))) := by
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
    exact h2
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63090222135974034153661880833 : ((p5 ∧ (((((True ∨ ((True → p1) → p4)) → p4) → p4) ∧ ((((p2 ∧ (False ∨ False)) ∨ (p1 ∧ (p2 ∧ p5))) → p2) → p3)) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219089474655148805822027195583 : ((True ∨ ((False ∨ True) ∧ True)) → (((((p5 ∧ True) ∨ p4) ∨ (p1 ∧ (((p1 ∨ p5) ∧ p4) → (((p4 ∨ p2) ∨ p2) → True)))) → p4) ∨ True)) := by
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
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356346639096071424068390824880 : (p5 → (((((((p2 → p5) ∨ (p2 ∧ False)) ∨ p4) → (p2 → p1)) ∨ p1) → p4) ∨ ((p2 ∨ ((p1 ∨ False) ∨ ((p1 → p2) ∨ True))) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111667396614296826675301225338 : ((((p3 ∨ (p5 → (p5 ∧ (((p2 ∨ p2) ∧ p4) ∨ ((((p1 → p1) ∧ True) → (False ∧ (p3 → False))) ∧ False))))) ∨ True) ∨ p3) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196781544529791467788173468764 : ((((p1 ∨ p4) ∧ ((p2 → p3) → p4)) ∧ False) ∨ (False ∨ (False → ((((((p1 ∧ p4) ∨ p4) ∧ p1) → (p2 ∧ p4)) → (True → False)) → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729580651833096219775223834635 : (((((p4 ∨ p1) ∨ True) → ((p3 ∨ (p3 → ((p5 → (p2 ∨ False)) → ((p2 ∧ (True ∨ p5)) ∧ ((p1 ∨ (p3 ∨ True)) ∨ True))))) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158604125971077259844148747024 : ((False ∧ ((((p1 → True) ∧ ((p4 ∨ ((p2 ∨ p3) ∨ True)) → (p1 → p4))) ∧ True) → (False ∧ False))) ∨ (((True → (p5 → True)) ∨ True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174391759345475847070005170136 : (((p1 ∧ ((False ∧ (p3 ∨ p4)) → (p1 ∨ False))) ∧ ((p5 ∧ p5) ∨ (True → p5))) → (((p3 → False) → p4) ∨ (((p2 ∧ False) ∨ False) → p5))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- False on the left can always be used.
      apply False.elim h13
  case inr h14 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h15
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- False on the left can always be used.
      apply False.elim h18
    case inr h19 =>
      -- False on the left can always be used.
      apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_73253244074459224067774094640 : (((((True → (True → (False ∨ False))) ∧ (p1 ∨ ((p2 ∧ True) → (p5 ∨ (p4 ∧ (((True → p2) ∧ p1) → True)))))) ∧ (p1 → p3)) ∨ False) → p5) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h8 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h9 := h5 h8
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h10 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h11 := h9 h10
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- False on the left can always be used.
        apply False.elim h12
      case inr h13 =>
        -- False on the left can always be used.
        apply False.elim h13
    case inr h14 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h15 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h16 := h5 h15
      -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
      have h17 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h16, we can now drive its conclusion.
      let h18 := h16 h17
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- False on the left can always be used.
        apply False.elim h19
      case inr h20 =>
        -- False on the left can always be used.
        apply False.elim h20
  case inr h21 =>
    -- False on the left can always be used.
    apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_5240763062009598290264913333 : (((((((((((False ∧ p4) → p3) ∨ (((False → p1) → (True ∨ False)) → p4)) → (p4 ∨ p3)) ∨ p3) ∨ p5) → False) ∧ p5) → p1) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((((((False ∧ p4) → p3) ∨ (((False → p1) → (True ∨ False)) → p4)) → (p4 ∨ p3)) ∨ p3) ∨ p5) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809223774694359282512008556018 : (((p5 → (((((False → p4) → p5) ∨ (((p3 → (p4 → p3)) → ((p5 ∧ p5) ∧ (p3 ∧ p4))) → p2)) → (p4 → (False ∨ p4))) ∨ p3)) ∨ p1) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149653374315568294583270798914 : ((p4 ∧ (((True → p3) → False) ∨ (((True ∨ False) → p2) → ((p3 → False) ∨ ((True ∧ (p2 → True)) ∧ p5))))) ∨ ((p1 ∧ (p1 → p2)) → p1)) := by
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
theorem thm_5_vars_207517064509498224470262853163 : (((((p5 → True) ∨ p4) ∧ p5) → p4) → (((((((True ∨ p3) ∧ False) → False) → p3) → p3) → (p2 ∨ False)) → (p4 ∨ (p5 ∨ (p4 → p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (((((True ∨ p3) ∧ False) → False) → p3) → p3) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : (((True ∨ p3) ∧ False) → False) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h10 =>
        -- False on the left can always be used.
        apply False.elim h9
      case inr h11 =>
        -- False on the left can always be used.
        apply False.elim h9
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h12 := h5 h6
    -- One of the premise coincides with the conclusion.
    exact h12
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h13 := h2 h4
  -- Disjunctions on the left can always be decomposed.
  cases h13
  case inl h14 =>
    -- One of the premise coincides with the conclusion.
    exact h14
  case inr h15 =>
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45398107177321235169409888934 : (((p5 ∧ ((((((True ∧ False) ∨ (p2 ∨ (p4 ∧ False))) ∧ p4) → ((p2 → (p3 → p1)) → p5)) ∧ p1) → ((p1 ∨ p5) ∨ p4))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148424458833380105419458002448 : ((((True ∧ (p5 ∨ (p3 → p1))) ∧ (((p4 ∧ True) ∧ (p1 ∨ p3)) → p5)) → (p3 ∨ (p1 ∨ (p3 → False)))) ∨ (p5 → ((p1 ∧ p5) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55324587176730048372541883249 : (((p3 ∨ ((p2 ∧ (p5 ∨ p2)) ∧ p5)) ∨ ((p5 ∨ (True ∧ (p2 → (p1 ∨ p2)))) ∨ ((p4 → ((p4 → p4) ∧ (p5 ∧ p2))) → False))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150306139451660725866695938849 : ((p4 → (((p5 → p4) → (p1 ∧ True)) → (((p4 ∧ (p5 ∧ p5)) ∧ ((True ∧ (p5 ∨ p4)) → p1)) ∨ p2))) ∨ ((True ∨ (True ∨ p1)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157580872585364864183267667414 : ((((p1 → p4) → (p4 ∨ (p3 ∧ (p3 ∨ (p4 ∨ (((p1 ∨ p5) ∨ p3) → False)))))) → (p5 ∧ p5)) ∨ ((False ∨ p4) ∨ (True ∧ (False → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196814594059021465315373985890 : (((True ∧ (((p4 → p2) → p4) → p2)) ∧ p5) ∨ ((p1 ∧ ((True → p5) ∧ (True ∧ (p2 → p5)))) ∨ (((False ∧ p3) → (False → p3)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179330313209022917535561741382 : ((p1 ∨ ((((False ∨ ((True ∧ p3) ∧ p1)) ∧ p3) ∧ p3) ∧ (True ∧ p5))) ∨ (((p3 → p5) ∨ (p5 ∧ (p5 ∧ (p5 ∧ False)))) → (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209497716086104669163980968946 : ((p3 → (False → (p5 ∧ (True ∧ p5)))) → ((((p3 ∧ p4) ∨ (p4 ∨ (p4 → ((True → (True → ((p5 ∨ p1) → p2))) → p2)))) ∨ True) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226058581300616624580744132360 : (((p5 ∧ p3) ∨ p2) ∨ (((((False → (p1 ∧ p1)) ∨ (p1 ∧ ((p3 → (p2 → p5)) ∨ (p3 → True)))) ∨ True) → (p4 ∧ p2)) ∨ (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53866420980489717029636888866 : ((((p3 ∧ p5) ∧ ((((p4 → p5) ∧ p4) → False) ∧ p5)) ∨ ((p5 → True) → ((((p2 ∧ ((True ∨ p2) → p4)) ∨ p5) ∨ True) ∨ False))) ∨ p1) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_387741626168665814160979694341 : (((((((((p2 ∧ (p3 → p4)) → p1) ∨ (p5 ∨ True)) ∨ p1) ∧ ((p1 ∨ (p1 ∧ p4)) ∨ (p2 → p3))) → ((p3 → False) ∨ p1)) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_51374940828819500624952333498 : ((((((p2 ∧ (((p4 → False) → p3) → p1)) ∧ ((p5 ∨ (False ∨ False)) ∨ p2)) ∨ p3) ∨ p4) → (p4 ∨ (False ∧ ((p1 ∧ p2) ∨ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191947004727990709529823850897 : ((True → (p1 ∨ (((p4 ∨ (p5 ∨ True)) ∨ p2) ∧ p5))) ∨ ((p5 → True) ∨ (((True → ((p4 ∧ p4) ∨ p5)) ∨ p1) ∧ (p4 ∨ (p3 → p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_592035620356615676527779926797 : (((((p4 ∧ ((p5 → (p1 ∧ (p1 → (((p2 → p2) → False) ∧ (((p2 ∧ p4) ∨ (p5 ∧ p3)) ∧ p4))))) ∧ p3)) ∨ (p3 ∨ True)) ∧ True) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197386395916751929523701797503 : (((p3 ∨ ((p4 ∨ (True ∧ p3)) ∨ False)) → False) ∨ ((p2 ∧ p5) ∨ ((((p2 ∧ (True ∧ True)) → (False → p2)) ∨ ((False ∨ p2) → p2)) ∨ p1))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299341441129889645513213865377 : (False ∨ (((p5 ∨ (False ∧ p5)) ∧ ((p2 ∨ p3) ∨ ((p1 ∧ ((p1 ∨ False) ∧ (p5 → (p2 ∧ p1)))) ∨ (((p1 ∨ p1) ∧ p2) ∨ p4)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150302602635721636018674612960 : ((p4 → ((p3 ∧ (((p4 → p1) → (p4 ∧ p5)) → p4)) ∨ ((True ∧ (True ∨ (p4 ∧ p2))) ∧ (p3 ∨ p2)))) ∨ ((p4 ∧ p1) → (True ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305009250816250582325309702797 : (p1 ∨ (((((True ∧ (p4 → p2)) → p3) → (False ∨ False)) → ((((p5 → p3) → p2) → (p2 ∧ (p4 → p3))) ∨ True)) ∨ ((p4 → p5) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200341537161770114144749246084 : (((p3 ∨ p4) ∧ ((True ∨ p1) ∧ (p5 → p2))) → (p1 → (True ∧ ((p5 ∨ (p4 ∨ True)) ∨ (p5 ∧ ((((p2 ∧ p5) → p4) → False) → True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h4.left
    let h12 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h13 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h14 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213235318094105347053928346621 : ((((p2 ∧ p3) → p2) ∧ p2) ∨ ((p5 ∨ ((((p4 ∧ (p4 ∨ False)) → True) ∧ True) ∧ (False ∨ ((False ∨ p5) ∨ True)))) ∨ ((p3 ∧ p2) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336190349057191269126366056316 : (p1 → ((((p1 ∧ (p5 → p2)) ∨ (True ∧ ((((True ∧ (True ∧ p5)) ∨ (False ∧ p2)) ∨ ((p3 → False) → p5)) ∧ p2))) ∧ (False ∧ False)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305094212012206133503368186049 : (p1 ∨ ((p5 ∧ ((False ∨ (p2 → p2)) ∨ ((p3 → (p2 ∨ ((p3 ∨ p1) ∧ (p2 ∨ (p1 → False))))) ∧ (p4 ∨ p1)))) → ((False ∨ False) ∨ True))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351546957469966485077477739768 : (p4 → ((p2 ∨ (((p2 ∧ ((True ∨ (False → True)) → p1)) → (True ∧ p4)) → (p5 ∨ (p2 ∨ p3)))) ∨ (((True ∨ (p3 ∧ p1)) → True) → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312968603309392643109510508292 : (p3 ∨ (((((((p1 → p2) ∧ p5) ∨ ((p5 ∧ (p4 → p5)) ∨ p1)) → False) ∧ ((p5 ∧ (True ∨ (True ∧ (p1 → p5)))) → p1)) ∧ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265861915586834144790108624922 : (True ∧ (p5 ∨ (p3 ∨ (((False ∨ ((p3 → (p4 ∧ True)) → ((p4 ∨ p1) ∧ p3))) ∨ True) ∨ (p3 ∨ ((True ∧ p4) → (True → (p2 ∨ p4)))))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_170054678187194576884438529395 : ((((p2 → (p2 ∧ (p4 ∨ (p1 ∨ (False ∧ p4))))) ∨ p1) → ((True ∨ p3) ∨ p5)) ∧ (True → ((False ∧ ((p3 ∧ (p3 ∧ p5)) ∧ p1)) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



