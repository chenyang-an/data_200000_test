variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621634178740871460120320733733 : ((((False ∧ (True ∧ ((p1 ∧ (False ∨ ((p5 ∧ (p1 ∧ p1)) ∧ ((p4 ∧ (((p1 ∨ p2) ∧ (p3 → p4)) ∧ p2)) ∨ p5)))) → False))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_726951260924634971149262976288 : (((((False → True) → p1) ∨ (((p4 ∨ (((False ∨ (True → p4)) ∨ (p1 → p1)) ∨ False)) ∧ (((True → True) ∧ True) ∨ (False ∧ p2))) ∨ p5)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66195742395430623336819995054 : ((p5 ∨ ((True ∧ (((p4 ∧ p4) → (((p1 ∨ ((False ∧ p5) ∧ p1)) → True) ∧ False)) → p3)) ∨ (((p5 ∧ p4) → (False → True)) ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_901394381454828160831676561439 : (((((((((p3 ∧ (p5 ∨ p5)) ∨ True) → (False → p3)) → (((True → False) ∧ True) ∧ p3)) ∧ True) ∧ True) ∧ (False ∨ ((False → p5) ∧ p3))) → False) ∧ True) := by
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
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h12 : (((p3 ∧ (p5 ∨ p5)) ∨ True) → (False → p3)) := by
      -- Implications on the right can always be decomposed.
      intro h13
      -- Implications on the right can always be decomposed.
      intro h14
      -- False on the left can always be used.
      apply False.elim h14
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h15 := h6 h12
    -- We need to get the left conjuct of h15 based on <expert-advice>.
    let h16 := h15.left
    -- We need to get the left conjuct of h16 based on <expert-advice>.
    let h17 := h16.left
    -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
    have h18 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h17, we can now drive its conclusion.
    let h19 := h17 h18
    -- False on the left can always be used.
    apply False.elim h19
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61881779348215533221512059741 : ((p2 ∧ ((p2 ∧ (((((((p5 → p2) ∨ p1) ∧ ((p4 ∧ False) → p3)) ∨ p3) ∧ (p4 → (p1 ∨ True))) ∨ p4) → p2)) ∧ (p2 ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113315526541654616052466556522 : ((((p3 → (False ∧ False)) ∧ (((p2 ∧ p2) ∧ (p3 ∧ (((True ∧ p3) ∧ True) ∨ (False ∧ p5)))) ∧ (p1 ∧ p5))) ∧ (p1 → p5)) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_877010448543984627537653304638 : (((((((p4 → (False ∧ p4)) ∨ (p1 ∧ True)) ∨ ((p5 ∧ p2) → False)) ∧ ((p5 → p5) → (((False ∧ p5) ∧ p3) ∨ p5))) ∧ (p3 ∨ p1)) → p5) ∧ True) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h8 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h9 : (p5 → p5) := by
          -- Implications on the right can always be decomposed.
          intro h10
          -- One of the premise coincides with the conclusion.
          exact h10
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h11 := h5 h9
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Conjunctions on the left can always be decomposed.
          let h13 := h12.left
          let h14 := h12.right
          -- Conjunctions on the left can always be decomposed.
          let h15 := h13.left
          let h16 := h13.right
          -- False on the left can always be used.
          apply False.elim h15
        case inr h17 =>
          -- One of the premise coincides with the conclusion.
          exact h17
      case inr h18 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h19 : (p5 → p5) := by
          -- Implications on the right can always be decomposed.
          intro h20
          -- One of the premise coincides with the conclusion.
          exact h20
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h21 := h5 h19
        -- Disjunctions on the left can always be decomposed.
        cases h21
        case inl h22 =>
          -- Conjunctions on the left can always be decomposed.
          let h23 := h22.left
          let h24 := h22.right
          -- Conjunctions on the left can always be decomposed.
          let h25 := h23.left
          let h26 := h23.right
          -- False on the left can always be used.
          apply False.elim h25
        case inr h27 =>
          -- One of the premise coincides with the conclusion.
          exact h27
    case inr h28 =>
      -- Conjunctions on the left can always be decomposed.
      let h29 := h28.left
      let h30 := h28.right
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h31 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h32 : (p5 → p5) := by
          -- Implications on the right can always be decomposed.
          intro h33
          -- One of the premise coincides with the conclusion.
          exact h33
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h34 := h5 h32
        -- Disjunctions on the left can always be decomposed.
        cases h34
        case inl h35 =>
          -- Conjunctions on the left can always be decomposed.
          let h36 := h35.left
          let h37 := h35.right
          -- Conjunctions on the left can always be decomposed.
          let h38 := h36.left
          let h39 := h36.right
          -- False on the left can always be used.
          apply False.elim h38
        case inr h40 =>
          -- One of the premise coincides with the conclusion.
          exact h40
      case inr h41 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h42 : (p5 → p5) := by
          -- Implications on the right can always be decomposed.
          intro h43
          -- One of the premise coincides with the conclusion.
          exact h43
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h44 := h5 h42
        -- Disjunctions on the left can always be decomposed.
        cases h44
        case inl h45 =>
          -- Conjunctions on the left can always be decomposed.
          let h46 := h45.left
          let h47 := h45.right
          -- Conjunctions on the left can always be decomposed.
          let h48 := h46.left
          let h49 := h46.right
          -- False on the left can always be used.
          apply False.elim h48
        case inr h50 =>
          -- One of the premise coincides with the conclusion.
          exact h50
  case inr h51 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h52 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h53 : (p5 → p5) := by
        -- Implications on the right can always be decomposed.
        intro h54
        -- One of the premise coincides with the conclusion.
        exact h54
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h55 := h5 h53
      -- Disjunctions on the left can always be decomposed.
      cases h55
      case inl h56 =>
        -- Conjunctions on the left can always be decomposed.
        let h57 := h56.left
        let h58 := h56.right
        -- Conjunctions on the left can always be decomposed.
        let h59 := h57.left
        let h60 := h57.right
        -- False on the left can always be used.
        apply False.elim h59
      case inr h61 =>
        -- One of the premise coincides with the conclusion.
        exact h61
    case inr h62 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h63 : (p5 → p5) := by
        -- Implications on the right can always be decomposed.
        intro h64
        -- One of the premise coincides with the conclusion.
        exact h64
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h65 := h5 h63
      -- Disjunctions on the left can always be decomposed.
      cases h65
      case inl h66 =>
        -- Conjunctions on the left can always be decomposed.
        let h67 := h66.left
        let h68 := h66.right
        -- Conjunctions on the left can always be decomposed.
        let h69 := h67.left
        let h70 := h67.right
        -- False on the left can always be used.
        apply False.elim h69
      case inr h71 =>
        -- One of the premise coincides with the conclusion.
        exact h71
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115530301512618775549334878128 : (((p2 ∧ ((True ∨ (True ∧ True)) ∧ (p2 ∧ p5))) → (True ∧ ((p1 ∨ False) ∧ (p1 ∨ ((p3 → (p5 → p4)) ∨ (p4 ∨ p5)))))) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111317490296455700218842940287 : (((p1 ∧ (((True ∨ (False ∧ p2)) ∨ (p4 ∧ (p4 ∧ (((p3 → True) → (False → p5)) ∧ p1)))) → ((False ∧ p5) ∧ p5))) ∧ p2) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225610443798324621449343283454 : (((p1 → False) ∧ p4) ∨ (((False ∧ (p1 ∧ (((True ∧ (p1 → False)) ∨ p5) ∨ (p2 → p5)))) ∧ p4) ∨ (((p4 ∧ True) → p5) ∨ (True ∨ p2)))) := by
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
theorem thm_5_vars_323835226867835682940464863754 : (p5 ∨ ((((p4 → (p5 → p5)) ∨ p2) → (((p5 → ((p5 ∧ p3) → (False → False))) ∧ True) ∧ p1)) → (((p2 → p4) ∨ (p5 ∨ p4)) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h4 : ((p4 → (p5 → p5)) ∨ p2) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h5
      -- Implications on the right can always be decomposed.
      intro h6
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h7 := h1 h4
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h11 : ((p4 → (p5 → p5)) ∨ p2) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h12
        -- Implications on the right can always be decomposed.
        intro h13
        -- One of the premise coincides with the conclusion.
        exact h13
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h14 := h1 h11
      -- We need to get the right conjuct of h14 based on <expert-advice>.
      let h15 := h14.right
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h16 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h17 : ((p4 → (p5 → p5)) ∨ p2) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h18
        -- Implications on the right can always be decomposed.
        intro h19
        -- One of the premise coincides with the conclusion.
        exact h19
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h20 := h1 h17
      -- We need to get the right conjuct of h20 based on <expert-advice>.
      let h21 := h20.right
      -- One of the premise coincides with the conclusion.
      exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111413753434545775846472712050 : (((p3 ∨ ((((((p4 ∧ p4) ∧ (p4 ∨ (p2 ∨ p5))) ∨ p2) ∨ p1) ∨ ((True ∨ (p3 → True)) ∧ (True ∨ False))) ∨ True)) ∧ True) ∨ (p4 → p2)) := by
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
theorem thm_5_vars_183697886241911453271268408153 : ((p3 → ((p4 ∨ p3) → ((False ∧ ((False ∨ p1) ∧ p5)) ∨ True))) ∧ (((p4 → True) ∧ (p1 ∧ p2)) → (p2 ∨ ((False → (p1 ∧ False)) → True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50656539946157773500720349867 : (((((p3 → p4) → ((True → (p2 ∧ p5)) ∧ p3)) ∧ (((p1 → (p5 ∨ True)) → p5) ∨ (p4 ∨ p4))) → (((p3 → p4) ∧ True) ∨ p5)) ∨ False) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : (p1 → (p5 ∨ True)) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h7 := h4 h5
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h9
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h12
      -- One of the premise coincides with the conclusion.
      exact h11
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64889696930826085133169516761 : ((p2 ∨ ((((((((p3 → p5) → (p1 ∧ p4)) ∨ (p3 ∧ (p3 ∨ p4))) ∨ (True ∧ p4)) ∨ p5) ∨ p4) → p1) ∨ ((p1 ∧ p3) → True))) ∨ p3) := by
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
theorem thm_5_vars_113490929849545798666824246715 : ((((p3 → ((((p5 ∧ (p5 ∨ ((p2 ∨ p2) → (False ∨ p1)))) ∨ (p1 ∧ p3)) ∧ p5) ∧ False)) → (p5 → p1)) ∨ (p3 → p3)) ∨ (p5 → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57692444616746507569602776203 : ((((True ∧ False) → p3) → ((((p5 → p3) ∧ (False ∨ ((((True ∨ (p5 → True)) ∧ True) → (p4 ∧ p3)) ∨ p2))) ∧ False) ∨ (True ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_626250915792906292741019529607 : ((((p3 → ((p4 ∨ ((((p1 ∨ p3) ∧ (p1 ∨ p5)) ∨ (False ∨ True)) ∧ True)) ∨ (((p5 ∧ (True ∨ p2)) ∨ (p2 ∧ p5)) → p2))) ∨ p2) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_609160020761206388879031402475 : (((((((p5 ∨ False) ∧ (p2 ∨ p1)) ∨ (True → (False ∧ (p3 ∨ (((p1 ∨ True) → ((p2 ∨ (p3 ∧ p4)) → p1)) → False))))) ∨ p5) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_165142744953182353064368659312 : ((((((p1 ∨ (((p1 → p4) ∨ p2) ∧ p3)) → p5) → p4) ∧ (p1 ∧ p4)) ∧ (p1 ∧ p1)) ∨ ((p2 ∨ True) ∨ (((p5 ∨ p4) ∧ p1) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_8097019917853423935178361372 : (((((((True ∨ p5) ∧ p1) ∧ p4) → ((p1 ∧ (p2 ∨ ((False ∧ (p2 ∨ True)) ∨ ((p5 ∨ p2) ∧ (p2 → p3))))) ∨ p4)) ∨ p2) ∨ p1) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181175320344022218618830531657 : ((p1 ∧ (((((p4 ∨ p3) ∧ (p4 ∧ p4)) ∨ p1) ∨ p2) → (p3 ∧ p5))) → ((p4 → p2) → (p5 ∨ (p2 ∨ ((p4 → p5) ∧ (p4 → p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : ((((p4 ∨ p3) ∧ (p4 ∧ p4)) ∨ p1) ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185434940993645361676119137849 : ((False ∨ ((p2 → ((p3 ∧ (False → p5)) ∨ (p1 → True))) → p1)) ∨ ((False ∧ (((p1 ∧ p4) ∨ False) ∧ (False → (p5 ∧ (p2 ∨ p3))))) → p4)) := by
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
theorem thm_5_vars_305003572865915355376320547052 : (p1 ∨ (((((True ∨ ((True ∧ (True → (False ∨ False))) → p2)) ∧ (p4 ∨ p3)) → False) → ((True → p5) → (p5 ∧ False))) ∨ ((p1 ∨ p3) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1002662727081683984419507889 : (((((((((p1 → p4) ∨ (p2 ∨ ((False ∧ ((p3 ∨ p1) ∨ p3)) ∧ p1))) → p5) → True) → p1) ∨ p4) ∨ (False → p2)) → p1) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((((p1 → p4) ∨ (p2 ∨ ((False ∧ ((p3 ∨ p1) ∨ p3)) ∧ p1))) → p5) → True) → p1) ∨ p4) ∨ (False → p2)) := by
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
theorem thm_5_vars_769395703816802464144203133491 : (((p5 ∧ (False ∧ (False ∧ (False ∧ (False ∧ (((((p4 ∨ (p4 → p2)) ∧ p2) ∨ (p5 ∨ (p1 ∧ (p2 ∧ (p3 → p1))))) ∧ p4) ∧ False)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112582573499573422752168666457 : ((((((((p1 → ((True ∧ p1) ∧ (p4 ∧ (p4 ∨ (p5 ∨ (p5 ∨ p1)))))) → p1) ∧ True) ∧ True) ∨ True) ∧ (True ∧ p2)) → False) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179530199731040813625432451849 : ((p1 → ((((False ∨ p2) ∨ (p4 → (p5 ∨ p5))) ∨ (p3 → p4)) ∨ p1)) ∨ ((((False ∧ p4) → False) ∨ ((p2 → (p2 ∧ p2)) → p5)) ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152346842969661506359364815009 : (((((p5 ∨ p1) ∧ p1) ∨ p4) ∨ ((p3 ∨ (((True ∨ (p1 ∧ p5)) ∨ ((p5 ∧ p2) ∧ p4)) ∧ False)) → False)) → ((p2 ∨ p2) ∨ (True ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Conjunctions on the left can always be decomposed.
      let h4 := h3.left
      let h5 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h4
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
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358060626970060149244627150626 : (p5 → (p1 ∨ (((p5 → (False ∨ p2)) ∨ (False ∧ p5)) ∨ ((False ∧ (((((True → (False → p2)) ∨ True) ∨ p3) ∨ (p1 → p1)) ∧ p4)) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300565077336209986498730395867 : (False ∨ ((False ∧ (((p4 ∨ p3) ∨ p5) ∨ ((((p3 → (p4 ∨ (False ∧ True))) ∧ p4) ∧ True) ∨ (p2 → p1)))) ∨ (False → (True ∨ (False → p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198693416351523979409095009115 : ((p4 ∨ (p1 ∨ (p1 ∧ ((p4 ∨ p4) ∧ p3)))) ∨ ((False ∧ p5) → ((p5 ∨ p5) → ((((True → p1) ∨ p1) → (p4 ∨ p3)) ∨ (p2 ∨ p5))))) := by
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
    let h4 := h1.left
    let h5 := h1.right
    -- False on the left can always be used.
    apply False.elim h4
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h1.left
    let h8 := h1.right
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694391252104206967819284841940 : (((((p2 → p5) ∧ (p2 → ((((True → True) ∧ p3) ∨ p5) → (False ∧ p2)))) ∨ ((p3 ∧ True) ∨ (((p4 → (p3 ∨ p1)) ∧ p2) → True))) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_262288276842392478199797950244 : (True ∧ ((((p3 ∧ ((((p1 ∧ p2) → ((p5 ∧ p4) → p3)) ∨ True) → False)) ∧ (p3 ∨ True)) → (p5 ∧ (p1 ∧ (p5 ∨ (p3 ∨ p5))))) ∨ p2)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h6 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : (((p1 ∧ p2) → ((p5 ∧ p4) → p3)) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h7
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h10 : (((p1 ∧ p2) → ((p5 ∧ p4) → p3)) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h11 := h5 h10
    -- False on the left can always be used.
    apply False.elim h11
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h12 := h1.left
  let h13 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h12.left
  let h15 := h12.right
  -- Disjunctions on the left can always be decomposed.
  cases h13
  case inl h16 =>
    -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
    have h17 : (((p1 ∧ p2) → ((p5 ∧ p4) → p3)) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h15, we can now drive its conclusion.
    let h18 := h15 h17
    -- False on the left can always be used.
    apply False.elim h18
  case inr h19 =>
    -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
    have h20 : (((p1 ∧ p2) → ((p5 ∧ p4) → p3)) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h15, we can now drive its conclusion.
    let h21 := h15 h20
    -- False on the left can always be used.
    apply False.elim h21
  -- Conjunctions on the left can always be decomposed.
  let h22 := h1.left
  let h23 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h24 := h22.left
  let h25 := h22.right
  -- Disjunctions on the left can always be decomposed.
  cases h23
  case inl h26 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h26
  case inr h27 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709582260637672981192780766305 : ((((p1 ∨ ((((p4 ∧ True) ∨ p4) ∨ p2) ∨ False)) → (p3 → ((p1 ∨ p1) ∧ (((p3 ∧ p4) → p1) ∧ ((p2 ∨ (False → p2)) → p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48017104006011626153084343612 : (((((False ∧ ((((True ∧ True) ∧ p2) → p3) ∧ (True → p3))) ∧ True) ∨ ((p1 ∨ p1) ∧ (p3 → ((p3 → True) ∧ False)))) → (p3 ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38394791718515296248047957072 : (((((p5 ∨ p3) ∧ ((((p4 → False) ∨ (p3 ∧ (p3 ∧ True))) ∧ (p5 ∨ p2)) ∧ p4)) → (True ∧ (p4 → ((p2 ∨ False) ∨ True)))) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1113954462150043602018195259 : (((((p1 ∨ p5) ∨ p3) ∨ ((p1 → ((p5 → p5) → True)) → (False → p2))) → (p4 ∧ (p2 ∧ ((True ∨ p1) → (False ∧ p3))))) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p1 ∨ p5) ∨ p3) ∨ ((p1 → ((p5 → p5) → True)) → (False → p2))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : (True ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h9 := h7 h8
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152195887099399196103861926369 : (((p2 ∨ ((p3 → p5) → (False ∧ (p4 → p3)))) → (p2 ∨ (((p3 ∧ (p4 ∧ (p3 ∨ False))) ∨ p5) → p1))) → (p1 → (p1 ∨ (True → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178458352239396746322587848545 : (((p4 ∧ (False ∨ ((p4 ∨ (p4 ∧ p5)) → True))) ∧ ((p3 ∧ p2) ∨ p3)) ∨ ((False ∨ True) ∨ ((True ∧ ((p2 → (p3 → p2)) → p1)) ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64055395546740441974792639117 : ((False ∨ ((((p4 → (p3 ∧ False)) ∨ ((p2 ∧ ((((True ∨ p3) ∧ False) ∧ False) ∧ True)) ∧ True)) ∧ p2) ∨ (p5 ∨ ((False → True) ∨ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58443614638055099238005963057 : (((p3 ∨ False) ∧ (p2 ∨ ((p3 ∧ (p3 ∨ (((p5 → p2) → ((False ∧ p2) ∧ ((p5 ∧ True) ∨ ((p3 ∧ p1) → p2)))) ∨ p1))) → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118123904666344163693856715089 : ((False ∨ ((True → ((p5 → (True ∧ (False ∨ p4))) ∨ ((p5 ∨ (p1 ∨ ((p2 ∧ p5) ∧ True))) → (True → p1)))) ∧ (p3 → p4))) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340992683909069862214874993531 : (p2 → (((False → p2) → ((p2 ∧ (p5 ∨ False)) ∨ ((((p1 ∧ p3) ∨ (p1 → p5)) ∧ False) ∨ (((p4 ∨ p3) → (p2 ∧ p5)) ∧ p3)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60445689118483045975795751728 : (((p5 → True) → (p5 ∨ (((((p2 ∨ p4) ∨ True) ∨ (p2 ∧ p4)) ∧ p1) → ((p2 ∨ ((p3 ∨ (p2 → p2)) → (p4 ∧ False))) ∨ True)))) ∨ p5) := by
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
  cases h3
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
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
    case inr h9 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54621438406228033812536918959 : (((((((False → True) → True) ∧ True) ∨ False) ∧ p5) → (((((False → p1) → ((p2 ∨ p3) ∧ False)) ∧ ((p4 ∨ p3) ∧ True)) ∨ p3) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49516730166763550913280254938 : (((((p1 → ((p5 ∧ p4) → p3)) → ((p1 → (p2 ∨ (((p3 ∧ p1) ∨ p5) ∨ p5))) → False)) ∧ (False → p2)) → ((p1 ∨ False) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218160521931449140059941348328 : (((True ∧ True) ∨ (p5 ∨ p4)) → (p2 ∨ ((True ∨ ((p5 ∧ p3) ∧ False)) ∧ (((True ∧ (p3 ∨ (p1 ∨ p5))) ∨ True) ∨ (p1 ∨ (False → p1)))))) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_778461716090817439988596956219 : (((p1 ∨ (p4 ∧ ((p3 ∨ (((p1 → (p2 → p3)) → p5) → (((False ∧ p1) → p1) ∧ (p5 ∧ ((p4 → p1) → (p4 → True)))))) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704727816688933029092413366403 : ((((p2 ∧ (p2 ∨ (((p2 ∧ (True ∧ p5)) ∨ p2) → p1))) → ((((p4 ∧ p2) ∨ True) ∧ p5) ∨ (((True ∧ (p1 ∨ True)) ∨ True) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140486982812017501402524811644 : ((((((p3 ∨ False) → ((((p4 ∨ (p1 ∧ True)) ∨ p3) ∧ p3) → p3)) → p5) → True) ∧ (True ∨ (p5 → (True ∧ p2)))) → ((p1 ∧ p5) → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191461189352338244452058988722 : (((p4 → p3) → ((p2 ∨ ((p4 → p1) ∧ p4)) ∧ p3)) ∨ (((((p4 ∧ p5) ∧ ((p2 → (True → p1)) → p2)) ∨ p1) ∧ (p1 ∧ False)) → False)) := by
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
    let h7 := h5.left
    let h8 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h3.left
    let h10 := h3.right
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h3.left
    let h13 := h3.right
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150263305247881950829578140440 : ((p3 → ((False ∧ p3) ∨ ((((False ∧ p2) ∧ True) ∨ ((((p3 → False) ∨ p1) ∨ (p3 → False)) → p2)) ∨ True))) ∨ (p1 ∨ (p4 ∨ (p4 → p4)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_740079761337591347548868826323 : ((((False ∨ p2) ∨ ((False ∧ ((p4 ∧ (p4 ∨ (p4 → p5))) → (p2 ∨ (p5 → ((p1 ∧ (p2 ∨ (True → (p3 ∨ p4)))) → True))))) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318654971558767141780030171210 : (p4 ∨ ((p3 → (((((p5 ∧ (((p1 → p4) → False) ∨ (False → (False → False)))) ∨ (p1 ∨ True)) → (p5 ∨ p4)) ∧ p2) ∧ p1)) ∨ (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118182313580201515162019032309 : ((False ∨ (p4 ∧ (p5 ∨ (p1 ∧ (((p5 ∧ (((p3 → (True ∧ p2)) ∧ False) ∧ (p3 ∧ p5))) ∧ False) ∧ ((p5 ∨ p3) ∧ p4)))))) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149863671958220208884126992443 : ((p2 ∨ ((((True ∧ (((p4 → (((False → True) ∨ True) → p5)) ∨ p3) ∨ p3)) ∨ (True ∨ p4)) ∨ p3) ∨ False)) ∨ (((p1 → False) ∨ p1) → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_148265033833151900708098879122 : (((p5 ∨ (p3 ∧ ((False ∧ ((True → (p4 ∨ True)) → p5)) ∧ ((p2 → p5) ∧ p4)))) ∨ (p4 → (p4 ∨ p2))) ∨ (p5 ∨ ((False → p5) → p4))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58705613205521999438788146843 : (((p2 → p5) ∧ ((((((False ∧ (p2 ∨ p3)) ∨ True) ∧ p4) ∧ p1) → ((False ∧ False) ∨ False)) ∨ (((p3 → True) → p3) → (p1 ∧ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160073841775344144795442416592 : (((True ∨ (((p1 ∨ (p4 ∧ ((p2 ∧ (p1 ∨ (p4 ∧ p1))) ∧ (p5 → p4)))) ∨ True) → p5)) → False) → ((((False ∨ p2) ∨ p4) ∨ p5) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ (((p1 ∨ (p4 ∧ ((p2 ∧ (p1 ∨ (p4 ∧ p1))) ∧ (p5 → p4)))) ∨ True) → p5)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113382073767566482213135794061 : (((p4 ∨ (p3 → ((True ∧ True) → ((p3 ∧ (False ∧ (p5 ∧ (p5 ∧ False)))) ∨ (p4 → ((False ∧ p3) → p1)))))) ∧ (False → False)) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207507556477149141078457126269 : (((((p5 ∨ p3) ∧ p2) ∧ p4) → p1) → ((((False ∧ (p1 → p5)) ∨ p5) ∧ p4) ∨ (((p3 ∧ p3) → ((False → (True ∨ p5)) ∨ p3)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180443127730815130263494355761 : ((((((p2 → p1) → p3) → p4) → (p3 ∨ (True → p1))) → (False ∧ p3)) → (((p4 ∨ p3) ∨ p4) → (p3 → (False ∧ (p4 ∨ (False ∧ p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h6 : ((((p2 → p1) → p3) → p4) → (p3 ∨ (True → p1))) := by
        -- Implications on the right can always be decomposed.
        intro h7
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h8 := h1 h6
      -- We need to get the left conjuct of h8 based on <expert-advice>.
      let h9 := h8.left
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h11 : ((((p2 → p1) → p3) → p4) → (p3 ∨ (True → p1))) := by
        -- Implications on the right can always be decomposed.
        intro h12
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h10
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h13 := h1 h11
      -- We need to get the left conjuct of h13 based on <expert-advice>.
      let h14 := h13.left
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h16 : ((((p2 → p1) → p3) → p4) → (p3 ∨ (True → p1))) := by
      -- Implications on the right can always be decomposed.
      intro h17
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h18 := h1 h16
    -- We need to get the left conjuct of h18 based on <expert-advice>.
    let h19 := h18.left
    -- False on the left can always be used.
    apply False.elim h19
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h20 =>
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h21 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h21
    case inr h22 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h23 : ((((p2 → p1) → p3) → p4) → (p3 ∨ (True → p1))) := by
        -- Implications on the right can always be decomposed.
        intro h24
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h22
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h25 := h1 h23
      -- We need to get the left conjuct of h25 based on <expert-advice>.
      let h26 := h25.left
      -- False on the left can always be used.
      apply False.elim h26
  case inr h27 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148367659102601716276901056679 : ((((False ∨ (True ∨ ((False → True) → (p5 → ((p1 → p1) → p1))))) ∧ False) ∨ ((False ∨ (True ∧ p2)) ∧ p3)) ∨ ((True ∧ p4) ∨ (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251318022571562302142562022678 : ((p2 → p3) ∨ ((p4 ∨ (p3 → (p2 ∨ (((False ∨ p1) ∧ p3) → p4)))) ∨ (p3 ∨ (p1 → (((p1 ∨ (p1 ∨ p5)) ∧ False) → (p2 → p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111338309244581545895809105756 : (((p3 ∧ ((((((p1 ∨ (True ∧ (p4 ∧ (True → p3)))) ∨ p3) ∧ p2) ∨ p1) ∧ (p5 → (p2 → True))) ∧ (p3 ∨ p2))) ∧ p3) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65762472770631509443374044556 : ((p4 ∨ ((((p1 → (True ∨ p2)) ∨ p4) ∨ (p3 ∨ ((((p5 ∧ p5) → False) ∧ (p2 ∧ p5)) ∧ p3))) → ((p5 → (p2 → p3)) → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116602092209533217747450262570 : (((p5 ∨ p5) ∧ (((False ∨ p5) ∨ ((p2 → ((False → ((p3 → p5) ∨ p5)) ∧ ((p3 ∧ p1) → (p4 ∧ p3)))) → p4)) → False)) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313988880927338153940419395939 : (p3 ∨ (((p5 → ((p3 ∨ False) → p4)) → ((((p2 → ((((p1 ∧ p2) → p1) ∧ (True → p3)) → p5)) → p1) ∨ p4) ∨ p2)) ∨ (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172113365404824256499188115841 : (((((False → (False → False)) ∧ (False ∨ (p5 ∧ p3))) ∧ p3) ∧ (p4 ∨ (False → p2))) ∨ (True ∨ (p4 ∧ (((p2 ∨ p2) ∨ (True ∧ True)) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250872157467460485781681615358 : ((p1 → p3) ∨ ((p1 ∨ (p4 ∨ ((p2 ∧ (((p1 → ((True ∨ (p3 → p4)) ∨ (p1 ∨ p1))) → p4) ∨ (p5 ∨ (p2 ∧ p4)))) ∨ True))) ∨ p4)) := by
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
theorem thm_5_vars_225237609820305642108375492322 : (((p5 ∧ p4) ∧ p2) ∨ (((((p4 ∧ p4) ∧ (p2 ∨ p3)) → p5) ∨ ((p4 → True) ∨ (((p1 → p1) → (p5 → p2)) ∨ p3))) ∨ (False → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114580869989096112443641841622 : ((((p4 ∧ (((p2 ∧ p5) → p3) → p1)) ∨ ((((p4 ∨ p2) ∨ p3) → p4) ∧ p2)) ∧ ((p3 ∨ (p1 ∧ (p3 → True))) ∧ p1)) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186504701489743341513654946276 : (((p5 ∨ ((p2 ∨ p4) → ((p2 → p1) → p3))) ∧ (True ∧ p1)) → (((p4 → p5) → (p3 ∨ True)) ∨ (((p3 ∨ p4) ∨ p3) ∨ (True → False)))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h3.left
    let h10 := h3.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h11
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147831017989386459502940340768 : (((p1 ∨ ((True ∧ (p2 ∨ (False → p4))) ∧ (((((p2 ∧ p5) ∨ p5) ∨ (True → p5)) → p5) ∨ p4))) → p2) ∨ (((False ∨ p2) ∧ False) → p4)) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156679845573654818553111290137 : ((((True ∧ (((p1 ∧ (p5 → (p5 → p3))) → ((p2 → p5) ∧ p5)) ∨ False)) ∨ (True ∨ p2)) ∧ p5) ∨ (True ∨ (((False → p1) ∨ p4) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150062842671700435457009010700 : ((True → ((((p5 ∨ (p2 → (False → (False ∧ (p4 → p2))))) ∧ (p4 ∧ p2)) ∨ p1) ∧ (p1 ∧ (True ∧ p4)))) ∨ (p5 ∨ (p1 → (True ∨ p4)))) := by
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
theorem thm_5_vars_43426270807207357165920971665 : ((((((((True ∨ p2) ∨ p3) → p4) → p1) → (((p5 → (p4 → (p1 → (p1 ∧ p4)))) ∧ (True ∨ (False ∨ p5))) → p1)) ∨ p2) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121366342006051256754528963364 : (((((p3 ∧ ((p4 ∨ (p4 → ((p1 ∧ True) ∧ ((p1 ∧ p2) → (p5 ∨ (p2 → True)))))) ∧ (p1 ∧ p3))) ∨ True) ∨ p1) → False) → (p4 ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p3 ∧ ((p4 ∨ (p4 → ((p1 ∧ True) ∧ ((p1 ∧ p2) → (p5 ∨ (p2 → True)))))) ∧ (p1 ∧ p3))) ∨ True) ∨ p1) := by
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
theorem thm_5_vars_134461006405928154419632050890 : (((((p3 ∧ ((p4 ∧ True) → True)) → (p1 ∨ ((((p4 ∨ (True → p3)) ∧ True) ∨ (p1 ∨ False)) ∧ True))) ∧ True) → p1) ∨ (p4 ∨ (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137382792488742753215214112931 : ((p3 ∧ ((False → ((p4 ∨ p1) ∨ p5)) ∧ ((p5 ∧ ((p1 → p3) ∧ p1)) ∨ ((p1 → (True ∨ p1)) ∧ (p4 ∨ p3))))) ∨ ((False → p3) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207060846576378487760522781087 : (((p1 ∧ (p1 ∧ (True ∧ p5))) ∧ p5) → ((p2 ∧ ((((p5 ∨ (p2 ∨ p3)) ∨ ((p4 ∧ True) ∨ False)) → True) → ((p4 ∧ p4) ∧ p3))) ∨ p5)) := by
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
  let h8 := h7.left
  let h9 := h7.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54293125828151042645262539551 : ((((p3 ∨ p1) ∧ ((False ∧ p5) ∧ (p2 → False))) ∧ (((((False ∧ True) → p5) → p2) ∧ (p2 ∨ (p5 → (False ∨ (p2 ∧ p1))))) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149080721650412180732824480210 : ((((p5 ∨ False) → p2) → (((p1 → p1) → (p5 ∧ False)) → ((p3 ∨ (p3 ∨ (False ∧ (p5 → p3)))) ∨ True))) ∨ ((False ∧ p2) → (p2 ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256964314583901922149267517045 : ((p1 ∨ p5) → ((((((p1 ∨ (p3 ∧ (False ∨ p5))) ∧ p2) → p4) ∨ False) → p5) ∨ (True ∧ ((p3 ∨ (p3 → p4)) → (p4 → (p3 → True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351644787934293087632057621936 : (p4 → (((p4 ∨ p5) → (p2 ∨ ((p3 ∨ (p3 ∧ (p3 ∧ p4))) → (p3 ∧ (p5 → p2))))) ∨ (p5 → (((True ∧ True) ∨ False) ∨ (True → p1))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314419709489011969184015435139 : (p3 ∨ ((((p3 → False) → (((p3 ∨ p1) → (p1 ∨ False)) ∧ (p5 ∧ True))) ∧ (p3 ∧ ((p2 → False) ∧ False))) ∨ ((p2 → (True ∧ p1)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621066926712970732380709762348 : (((((p2 → p1) → (p2 ∨ (((((((True ∨ True) → p2) ∨ p1) → ((p1 ∧ (p4 ∨ True)) → (p4 → p2))) ∨ False) ∨ p5) ∨ True))) ∨ p3) ∨ p5) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338822080827352857670052244606 : (p1 → ((p4 ∨ p2) ∨ (((True ∧ (False ∨ (p2 → ((p4 ∨ p1) ∧ (p4 ∨ True))))) ∨ (p1 ∧ (p3 ∧ ((p5 → p5) → p3)))) ∨ (p2 → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_810072830735293206834220666191 : (((p5 → ((((p4 → p5) ∧ ((p5 → p5) → (p5 ∨ (p3 → p4)))) → (p3 ∧ ((True ∧ p4) ∧ False))) ∨ (p5 ∨ (p1 ∨ (p4 → p5))))) ∨ False) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_797317418376894745541924407905 : (((p1 → (((p5 ∧ (((p1 → (True ∧ p5)) ∧ ((p3 → p1) ∧ (p4 ∧ (p4 ∧ (p4 ∨ p2))))) ∨ p3)) ∨ (p5 → (p2 ∨ p3))) ∨ p1)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_225120991528758249954936561169 : (((p2 ∧ p4) ∧ p4) ∨ ((((p1 ∨ p5) ∨ (p2 ∧ p1)) ∨ (((((p1 ∨ (True → ((p5 ∨ p2) → p1))) ∨ p3) → True) → p1) → p1)) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p1 ∨ (True → ((p5 ∨ p2) → p1))) ∨ p3) → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344395523455142975224586598772 : (p2 → (p4 ∨ (True → (((p2 ∧ p1) ∨ p4) → ((((p5 → p4) ∨ (p2 → False)) → False) ∨ (((((p3 → p1) ∨ p5) ∧ p5) → p5) ∨ False)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h11 =>
      -- One of the premise coincides with the conclusion.
      exact h9
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h13
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h16 =>
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h17 =>
      -- One of the premise coincides with the conclusion.
      exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302636226717959058852741272025 : (False ∨ (p2 ∨ (((p4 ∧ (p4 ∧ (((False → p4) ∨ True) ∨ p3))) ∧ (p3 ∧ (True ∧ (p2 ∧ (True → p5))))) ∨ (p5 → (p5 ∧ (True → True)))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690342632216912356436890127160 : ((((p3 → ((p4 ∧ (p2 → ((p2 → False) ∧ p5))) → (p4 ∧ ((p2 ∨ p3) ∧ False)))) ∨ (((p2 ∨ (p4 ∧ p3)) → (p3 ∧ p3)) → True)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_194216891047088436802571029690 : ((p3 → (p3 ∧ (p3 ∧ (True ∧ (p1 ∨ (p1 ∧ p4)))))) → (((((True ∨ (p2 → True)) ∨ p3) → (True ∧ p5)) → (False ∧ p2)) ∨ (True ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233675715255731617442597745769 : ((p2 ∨ (False → True)) → ((((p2 ∧ p3) ∨ p2) ∨ True) → (((((p2 ∧ (p4 → (p3 → True))) ∧ p1) → p5) ∨ True) ∧ ((p1 → True) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
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
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h19 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h20
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h21 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h22
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h23 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h24 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h25
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h26 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h27
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h28 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h29 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h30
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h31 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h32
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_692355990677588775360974373208 : (((((((p2 ∧ (p3 ∨ p1)) → True) ∨ (p3 ∧ (False → (p2 ∧ p5)))) → p3) ∧ ((p3 ∧ (p2 ∧ ((p4 → (True → p4)) ∧ p2))) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164894340601065744252916836713 : (((p5 → (p5 ∧ (p4 ∨ (p2 ∨ (((((p1 ∨ True) ∧ p5) ∨ p1) → False) ∧ p4))))) ∨ p5) ∨ ((p3 ∧ ((p5 → p5) ∧ False)) → (p5 ∨ p5))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618961843583829176572711467730 : ((((((p5 ∨ p3) ∧ p4) ∨ (((True ∧ (p5 ∧ p5)) ∨ p2) ∧ ((((True ∧ (((False → p2) ∨ p5) ∨ True)) ∧ p3) ∧ False) → False))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



