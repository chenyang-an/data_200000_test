variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624214679450881481268343471889 : ((((p3 ∨ ((p2 → (((p5 → (p2 → p5)) → ((True → p5) ∧ p5)) → ((((False ∧ (p2 ∧ p4)) ∧ p5) ∧ p3) ∧ False))) ∧ p5)) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_47797425322494259080000399951 : (((((((p3 ∨ True) ∨ ((p3 ∧ (p4 ∨ p4)) → ((p5 → ((False ∧ p4) ∨ False)) → p3))) ∧ (p4 ∨ True)) → False) → p1) → (p1 ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_673897684833160439958717559330 : (((((p2 ∨ p5) → ((True ∧ True) ∨ ((((True ∧ p4) → p3) ∧ ((p4 ∧ p5) ∨ p1)) → (p2 ∧ (p5 ∨ False))))) → (p1 ∨ (p3 ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171363834911158415011235856927 : ((((((p1 ∨ ((p4 ∧ True) ∨ p3)) ∧ True) ∧ (True ∧ p4)) ∨ (p1 → p2)) ∧ p4) ∨ (p1 → ((((True → p5) ∧ (p1 → p5)) → p4) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256052600755492354153603286086 : ((True ∨ p4) → ((((p5 ∨ (p4 ∧ p5)) ∨ (p5 ∨ True)) ∧ (p1 → (p3 ∨ (p2 ∨ p4)))) → ((((p5 ∧ True) ∨ p4) ∨ p5) → (p4 ∨ True)))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h2.left
      let h9 := h2.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h12 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h13 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h13
        case inr h14 =>
          -- Conjunctions on the left can always be decomposed.
          let h15 := h14.left
          let h16 := h14.right
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h17 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h15
          case inr h18 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h18
      case inr h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h20 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h21 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h22 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h22
        case inr h23 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h24 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h25 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h25
    case inr h26 =>
      -- Conjunctions on the left can always be decomposed.
      let h27 := h2.left
      let h28 := h2.right
      -- Disjunctions on the left can always be decomposed.
      cases h27
      case inl h29 =>
        -- Disjunctions on the left can always be decomposed.
        cases h29
        case inl h30 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h31 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h26
          case inr h32 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h32
        case inr h33 =>
          -- Conjunctions on the left can always be decomposed.
          let h34 := h33.left
          let h35 := h33.right
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h36 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h34
          case inr h37 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h37
      case inr h38 =>
        -- Disjunctions on the left can always be decomposed.
        cases h38
        case inl h39 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h40 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h26
          case inr h41 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h41
        case inr h42 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h43 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h26
          case inr h44 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h44
  case inr h45 =>
    -- Conjunctions on the left can always be decomposed.
    let h46 := h2.left
    let h47 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h46
    case inl h48 =>
      -- Disjunctions on the left can always be decomposed.
      cases h48
      case inl h49 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h50 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h51 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h51
      case inr h52 =>
        -- Conjunctions on the left can always be decomposed.
        let h53 := h52.left
        let h54 := h52.right
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h55 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h53
        case inr h56 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h56
    case inr h57 =>
      -- Disjunctions on the left can always be decomposed.
      cases h57
      case inl h58 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h59 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h60 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h60
      case inr h61 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h62 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h63 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h63



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655550820663342884366927318793 : ((((((False → (p1 → ((False ∧ False) ∨ ((True ∨ ((p3 ∨ False) → p1)) → p3)))) → ((p2 ∧ p5) ∧ p2)) → (False ∧ p2)) ∨ (p1 ∨ True)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_3928972438256854840797854780 : (False ∨ ((True ∧ (p5 ∧ ((p2 ∨ p1) ∨ p3))) ∨ (p3 → (p2 ∨ (p1 → ((False ∨ p1) → (((p5 ∨ True) ∨ (p3 ∨ p3)) ∧ p3))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357230718008223407663490115227 : (p5 → ((p3 → p3) ∧ (((p1 ∨ ((p3 ∨ (p3 ∧ (p2 ∧ (p1 → (True → p2))))) ∨ (((p4 ∧ p5) ∧ p1) → False))) ∧ False) ∨ (True → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317928036302535630132093188932 : (p4 ∨ ((False ∨ ((((p5 → p2) → True) ∨ ((p3 ∨ (p2 ∧ p5)) ∨ (False → p4))) → (p4 ∨ (p1 ∨ ((p4 → p4) ∨ (p1 ∧ p2)))))) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h7
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h11
        -- One of the premise coincides with the conclusion.
        exact h11
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h13
      -- One of the premise coincides with the conclusion.
      exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_865119680629125362822830517467 : (((((p2 ∨ (((p3 ∨ p4) ∨ p2) ∨ p1)) ∨ ((p2 ∨ p4) → (False → ((p2 → (p5 ∧ (((p3 ∨ p1) ∨ False) ∨ True))) → True)))) → False) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p2 ∨ (((p3 ∨ p4) ∨ p2) ∨ p1)) ∨ ((p2 ∨ p4) → (False → ((p2 → (p5 ∧ (((p3 ∨ p1) ∨ False) ∨ True))) → True)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59744552136440289517444003411 : (((p1 ∧ p1) → (((p4 ∨ ((((p5 ∧ ((p5 → False) ∨ (True ∧ p4))) ∨ ((False ∨ False) ∨ True)) ∨ (p3 ∧ p5)) ∧ True)) → p5) → p5)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : (p4 ∨ ((((p5 ∧ ((p5 → False) ∨ (True ∧ p4))) ∨ ((False ∨ False) ∨ True)) ∨ (p3 ∧ p5)) ∧ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h5
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314929435818196190332427963927 : (p3 ∨ (((p2 ∨ p4) ∨ (((True → p3) ∨ p4) ∧ (False → p1))) ∨ (False → (p4 → ((False ∨ p3) ∧ (p4 → ((p4 ∧ False) ∨ (p4 ∨ False)))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43540263220450674125393032073 : ((((p3 → (p2 ∧ ((p5 ∨ (((((((p3 → (p2 → p1)) ∨ p5) ∧ (p3 ∨ p5)) ∨ p5) ∧ p5) → p1) ∧ True)) ∧ True))) ∨ p4) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136950840961506639477347948955 : (((True ∧ True) → (p4 ∨ ((p3 → p1) ∧ (p1 → ((((((False → True) ∨ p1) ∨ p2) ∨ (p2 ∧ True)) → True) ∧ p2))))) ∨ ((p4 ∧ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133701970501017048073127514690 : (((((p5 ∨ ((p2 ∨ (p5 ∨ (p2 → False))) ∨ p3)) ∧ ((p4 → p5) → p1)) ∧ (p2 → ((p1 → p1) → p5))) ∧ p1) ∨ ((p5 → p5) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187685136728497158364904829307 : ((False → (((p4 ∧ p3) ∧ (p5 ∧ (p2 ∨ (p2 ∨ p2)))) ∧ False)) → (True → (p2 → ((((True ∨ p1) ∧ False) → True) → (p5 → (p4 ∨ p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187320287907277518588485996397 : ((p1 ∧ (True → (((p1 ∨ (False → p3)) ∨ False) ∧ (p5 → p2)))) → (p2 → (((p4 ∨ p1) → p1) → (p3 ∨ ((p3 → p1) ∧ (p1 ∨ p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h6
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304793120382266443777619562599 : (p1 ∨ (((((((p2 ∨ p1) ∨ (((p2 → False) ∧ p2) → p3)) → True) → (p1 ∨ ((False ∨ (p1 ∨ False)) ∨ p2))) → False) ∧ p2) → (p3 ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((((p2 ∨ p1) ∨ (((p2 → False) ∧ p2) → p3)) → True) → (p1 ∨ ((False ∨ (p1 ∨ False)) ∨ p2))) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249669878418382650967857271961 : ((p5 ∨ p4) ∨ (((p4 ∨ ((p4 ∧ p3) → (True ∧ (p1 ∨ ((p2 → True) ∧ (False ∨ ((p3 → p4) → True))))))) → p2) ∨ (True ∨ (p1 → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152653657475253130738731520956 : (((False → p5) ∧ (((p4 ∨ ((p3 ∨ (p4 ∨ (p5 ∧ p1))) → True)) → False) ∧ (p1 → ((p3 → p4) → False)))) → (((p5 ∨ p1) ∨ True) ∧ p1)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h10 : (p4 ∨ ((p3 ∨ (p4 ∨ (p5 ∧ p1))) → True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h12 := h8 h10
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197312061413830892291600583872 : ((((True ∧ p5) ∨ (p3 → (True → p5))) → p2) ∨ (p3 ∨ (True → (p1 ∨ (p4 ∨ (((p4 ∧ ((True ∧ p3) ∨ p5)) ∨ (p1 ∨ False)) ∨ True)))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347298055567808785483828199272 : (p3 → ((p4 ∨ ((False ∨ p2) ∧ ((p1 → (p5 ∧ p4)) → p2))) ∨ ((p5 → (p5 ∨ ((p3 ∧ (p1 ∧ p3)) ∨ False))) → (p3 ∨ (p1 ∧ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322555910980679603394877343416 : (p5 ∨ ((p1 ∨ (((p3 ∧ (False ∨ (((p4 ∧ p5) ∨ p1) ∨ (False ∨ (False → (p3 → False)))))) ∨ ((p2 → p1) ∨ p2)) → (p4 ∨ True))) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
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
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h9
        case inr h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- False on the left can always be used.
          apply False.elim h13
        case inr h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47404191787475134298922786313 : (((True ∧ (p1 ∨ (((((((p1 → (p1 ∧ (p5 ∨ True))) → p3) ∧ p1) ∧ (p1 ∧ (p4 → p2))) ∧ False) ∨ p3) ∨ False))) ∨ (p3 ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606488735042006709399339562282 : (((((((p4 ∧ (p3 → (((p5 ∧ (p4 → (((p4 → p1) ∧ p2) ∨ (p4 ∨ p4)))) ∧ (p1 ∨ False)) → True))) ∧ p1) → p3) ∧ p5) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_752482260444426429432974694648 : (((False ∧ (((p3 → p4) ∧ (p4 ∨ (p5 → (((((p2 → False) → (False ∨ (p3 → p4))) → ((False ∧ p3) ∧ False)) → p1) ∨ p2)))) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149554177176596616826775779245 : ((p2 ∧ ((p1 ∨ (p1 → (p1 ∨ (True ∧ (p4 ∧ (p4 ∨ p4)))))) → ((p2 → p3) → (p2 → (p4 → False))))) ∨ ((p3 ∨ True) ∧ (True → True))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49011755706851444931160155864 : ((((((True → (((True → (True ∧ ((p4 ∨ p1) ∨ p2))) ∧ (p5 ∧ (True → p4))) ∧ p2)) ∧ p5) → p3) → p3) ∨ (p2 ∨ (p4 → True))) ∨ p3) := by
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
theorem thm_5_vars_789464923069939100589580328332 : (((p5 ∨ (((((p4 ∨ True) → True) → p4) → (((p4 → p5) → p5) → p1)) ∨ ((p1 → ((p3 ∧ (p5 ∧ (p5 ∧ False))) ∧ False)) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55276278118160226584992449817 : (((True ∧ ((p5 ∧ (True → p4)) ∨ p5)) ∨ (False ∧ (((p1 → ((True ∨ (False ∨ False)) ∨ (((p5 → p2) ∧ False) ∨ p4))) → p5) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167555856667384295811179911278 : ((((False ∨ (((False ∨ True) → (False ∧ ((False ∨ True) ∨ True))) ∨ p2)) ∨ p4) ∨ (p3 ∧ False)) → ((((True → (p4 ∧ p4)) → p4) ∧ p1) ∨ True)) := by
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
        -- False on the left can always be used.
        apply False.elim h4
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
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139354326531202203660547697361 : (((True → ((p4 ∨ (p2 → ((p3 ∨ (True → p4)) → (((False → True) → p3) ∧ p3)))) → ((p4 → p1) → False))) ∨ False) → ((p1 → p3) ∨ True)) := by
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
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134070007561921102163562421085 : ((((((((p5 ∧ (False ∨ ((p3 ∧ False) → p1))) → (p1 ∨ p5)) ∧ True) ∨ ((p3 ∧ p1) → p1)) → True) → p5) ∨ p1) ∨ (p5 ∨ (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185315905662091109240470139690 : ((p3 ∧ ((p5 ∧ ((p5 → False) ∨ (p1 ∨ p2))) ∧ (p1 → p2))) ∨ (((p1 → (True ∨ (False ∨ p4))) → ((p4 ∧ False) ∨ (False → p3))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354595588613423883951136274860 : (p5 → (((p3 → (((True ∨ (p4 ∧ (((p3 → (p3 ∨ p4)) → (p1 ∧ p5)) ∨ p2))) ∧ ((p1 ∨ p4) ∨ (p2 → True))) → False)) ∧ p2) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193269941699703139890051354122 : (((p3 → (p2 ∨ p2)) ∧ (p4 → ((p1 ∧ p1) → p5))) → (p5 → (p1 ∨ ((p2 → (p4 → True)) ∧ (p1 ∨ ((p2 → p5) ∨ (False ∨ p4))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h7
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_623640543370572389567794859971 : ((((p1 ∨ ((((p5 ∧ (p4 → p5)) ∧ ((((p4 ∧ p1) → False) ∧ (((p2 ∧ p4) → p1) → p4)) ∨ (True ∧ False))) ∧ p4) ∧ p4)) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_105517442986917066579864740171 : (((p2 → ((p4 ∨ (False ∧ ((((p2 ∨ True) ∧ p5) → p3) ∧ p5))) ∨ ((p4 ∧ p5) ∨ True))) ∨ (p1 → ((True ∧ p4) ∨ p2))) ∧ (True ∨ p2)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116711087801945749812683410799 : (((p1 ∧ p4) ∨ ((((True → True) ∨ True) → ((p1 → p3) → (p5 ∨ p5))) ∧ (True ∧ (p4 → ((p3 ∧ (p3 ∨ p2)) ∧ p1))))) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40727418273436705784242687112 : (((((p2 ∨ (p2 ∨ (p4 ∨ (False ∨ False)))) → (((False ∨ (p2 ∧ p3)) → p5) → ((((False → False) → p4) → p3) ∨ True))) → False) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138174808539046654694342791213 : ((p1 → ((False ∧ (p5 ∨ (p3 ∨ (False → p2)))) ∨ (p1 ∧ (((True → (p5 → p4)) ∨ (p3 ∨ p2)) ∧ (p2 → p1))))) ∨ (p2 ∨ (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_629253433875954823603552145786 : (((((((((p2 → (((p3 ∨ p3) → (False → ((p1 ∧ (p3 → p5)) → True))) → p2)) → (p4 ∨ p5)) ∨ p4) ∨ True) → True) ∨ False) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607152285601439084074662327037 : (((((((True ∧ ((True ∧ True) ∨ False)) ∨ True) ∧ ((((p4 ∧ p4) ∨ ((True ∨ False) ∨ p3)) ∧ ((p4 → True) → p3)) ∨ p4)) ∧ False) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_322457757481121032952512892281 : (p5 ∨ (((p5 → (True ∨ p5)) ∧ ((((p2 ∧ ((p5 → (p1 ∧ p5)) ∨ p2)) ∨ ((p4 → (True ∨ False)) → False)) ∨ (p2 → False)) → p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698615111743409466574308457642 : (((((p2 ∨ (p5 → p4)) ∧ (((p2 → p4) → p2) ∧ (p5 ∨ False))) ∨ ((False ∨ p4) → (((p1 → True) ∨ ((p5 → p2) ∨ p1)) ∨ False))) ∨ False) ∧ True) := by
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
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_202399901018803286259388517758 : ((((p5 → True) → True) ∧ (False → p3)) ∧ ((False ∨ ((p4 → (((p2 → p5) ∨ p3) ∧ p5)) → p2)) ∨ (((p3 ∧ (p4 ∧ p5)) → False) → True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249908612278707705167970813457 : ((True → p1) ∨ ((((p2 ∧ p5) ∨ (False ∧ ((p4 → (p1 ∧ True)) → ((p4 → ((p2 → p5) → p5)) ∧ (p2 → p3))))) ∧ p5) ∨ (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117924645147821343262973126507 : ((p5 ∧ (((True ∨ p2) → p3) ∨ ((p5 ∧ p4) ∧ (((p3 → p4) ∧ ((p2 ∨ (p2 ∧ ((p3 ∧ p1) → False))) ∧ p2)) ∨ p5)))) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57399956474831231085354889803 : (((False ∨ (p3 ∨ p1)) ∨ ((p1 ∧ (((((p5 → p5) ∨ p3) → p2) ∨ p5) → (True ∧ (True ∧ ((p5 ∧ p3) ∧ (p5 ∧ p1)))))) ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65457303941600285683297559744 : ((p3 ∨ ((p1 ∨ p4) → (((((p2 ∨ (p3 ∧ p1)) ∧ p4) ∨ True) → ((((p5 → p2) ∨ p1) ∨ p2) ∧ False)) → (p1 → (False ∨ p4))))) ∨ p2) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : (((p2 ∨ (p3 ∧ p1)) ∧ p4) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_782344106958889450679736285589 : (((p3 ∨ ((((p4 ∧ ((p1 ∨ True) ∨ (((True → p2) ∨ (p5 ∨ p1)) ∧ p5))) ∨ (p1 → (p2 ∨ ((True ∧ True) ∧ False)))) ∧ p4) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138310074131426367943584576385 : ((p3 → ((p5 ∨ (p3 ∧ (p4 ∧ p5))) → (p1 → (p4 → (False ∨ (p3 → (((p3 ∧ p2) ∨ (p2 ∧ p4)) ∧ p4))))))) ∨ (p4 ∨ (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133992693369855411103929924354 : (((((((((p4 ∧ (p3 → p1)) → p1) → p3) ∨ p4) ∨ p3) ∧ (p5 ∨ (((False → p2) → p3) ∨ p1))) ∧ True) ∨ True) ∨ ((p5 ∧ p3) ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_717401122726730639533728303 : (((True → (((False ∨ (p1 → p5)) ∨ p3) ∧ True)) → ((p2 ∧ (((p4 → (False ∨ (True ∧ False))) ∧ p4) ∨ (p2 ∧ p5))) ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149952132217263867651227403765 : ((p4 ∨ (((((p3 ∧ (True → (False → (((p4 ∨ p5) ∧ (True ∨ p2)) ∨ p1)))) ∧ p4) ∨ p2) ∧ True) ∧ False)) ∨ ((False ∧ (p2 → False)) → p1)) := by
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
theorem thm_5_vars_707329194428532433594165511805 : ((((((True ∨ p2) → (False ∧ p2)) ∨ (p4 ∨ p2)) ∨ ((p2 ∨ (((False → p2) → (p1 ∨ (True → p5))) → (False → p3))) ∨ (p1 ∨ False))) ∨ p3) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319264632374447822953861358069 : (p4 ∨ ((((True ∧ (((p2 ∧ (p5 ∨ (p3 ∧ False))) ∧ p2) ∨ (False → False))) ∨ p3) ∨ p2) ∨ ((p4 ∨ (p5 → ((p4 ∧ p2) → p1))) → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2823255890276851177750888827 : ((((p3 → True) ∧ True) → p1) → ((((((p4 ∧ (p4 ∨ True)) ∧ ((True ∧ True) → p3)) ∨ (p4 ∨ (p5 → True))) → p3) ∧ True) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p3 → True) ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190070498679065827557038043555 : (((((p1 ∨ False) ∨ (True ∨ (True ∧ p4))) → p5) ∧ p1) ∨ (((((p5 ∨ (False ∨ p3)) ∧ p4) → p1) → (p5 → (p2 ∨ (p5 ∨ p5)))) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38966231634113757045080414966 : ((((True ∧ p3) ∧ (p2 → (p4 ∧ ((False ∧ (((p1 → (p5 → p1)) → ((p1 ∧ p2) → (False → (p5 ∧ False)))) ∧ p3)) ∧ False)))) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317625081030911491966238049797 : (p4 ∨ ((((((p2 ∨ (True ∧ ((p1 ∧ (p3 ∧ (p3 ∧ False))) ∧ ((p5 ∨ True) ∨ True)))) ∧ p5) → (p3 ∧ p1)) ∨ (p5 ∧ p2)) ∨ True) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171617815310473183106240663356 : (((((p5 ∧ p1) ∧ p2) ∧ (((p1 ∧ ((p3 ∧ True) ∧ False)) ∧ p4) ∧ False)) ∨ True) ∨ ((p2 ∧ p4) → (((p4 → p4) ∧ p3) ∨ (p4 ∨ p2)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60902588524501703545377306863 : ((True ∧ (p5 → (((((p3 ∧ p5) ∨ p1) ∧ True) ∧ p2) → ((((p4 ∨ p5) → True) → False) ∨ (((False → (p1 → p4)) ∨ False) ∨ p1))))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- False on the left can always be used.
    apply False.elim h10
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328698048549559612771732751722 : (True → ((((p1 ∧ ((p4 → (p4 ∨ p1)) ∨ (False → p3))) → p1) → p5) ∨ (((p4 ∨ ((p5 ∧ (p5 → (p4 ∧ p4))) ∨ p5)) ∨ True) ∨ p1))) := by
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
theorem thm_5_vars_786028255110179867925076612087 : (((p4 ∨ (((((((True → True) → (p2 ∧ p3)) ∨ p4) → (((p4 ∧ (p3 ∨ p3)) ∨ p2) ∨ (p4 ∨ True))) ∧ True) → True) → (p5 ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156864500082169039606013890416 : ((((((((p2 → False) ∧ (True ∧ p3)) ∨ p2) ∧ p4) ∨ (True ∨ ((p4 → False) ∧ p2))) ∧ False) ∨ True) ∨ (p5 ∨ (p1 → (p3 → (p3 ∨ p2))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788895217717165597075927833706 : (((p5 ∨ ((p3 ∧ (p3 ∨ ((p3 ∨ p1) ∨ (False ∨ (p3 ∧ (p3 → (True ∨ (((p4 ∧ p2) ∧ (p1 ∧ p5)) ∨ False)))))))) ∧ (True ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156895294067597568888984455273 : (((((p2 → False) ∨ (((p5 → p2) ∧ ((p5 → ((False ∨ p4) ∨ p2)) ∧ p2)) ∨ True)) ∨ p4) ∨ p2) ∨ (p5 ∧ ((p2 ∧ (p4 → p3)) ∧ p4))) := by
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
theorem thm_5_vars_187956146095652776176844459608 : ((((False → ((p2 → p5) ∧ False)) ∨ (True ∨ True)) ∧ True) ∧ (((p5 ∨ (True → p4)) → ((((p1 ∧ p4) → p3) ∧ (p4 ∨ p1)) → p2)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_696845864094414460714721026825 : ((((((((p5 → (p4 → p3)) ∨ p4) ∧ p2) ∨ True) ∧ (p5 ∧ False)) ∧ ((((((False ∧ p3) → p4) → True) ∨ p5) → (p1 → p5)) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184105874306030316959583290496 : ((((p4 → p5) ∧ (p4 ∧ (p1 ∨ ((p3 → p2) → p2)))) ∨ False) ∨ ((p1 → (((p1 → p2) → p2) → (p4 ∧ p5))) ∨ ((p5 ∨ True) ∨ False))) := by
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
theorem thm_5_vars_147350400889836440848629569140 : (((((((False ∧ p2) → p3) ∨ ((False → False) → (p3 ∧ p3))) → (p5 → False)) ∧ (False ∨ (p4 ∧ p3))) ∨ p3) ∨ (((p3 ∨ p2) ∧ p4) → p4)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111262452527907413068993206522 : ((((True → p2) ∨ ((p5 ∧ (((p2 ∧ p1) ∨ p4) → p2)) → ((True ∨ False) ∧ (p5 ∧ ((True ∧ p2) ∨ (False ∧ p3)))))) ∧ p3) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180317311946770706947199491787 : (((((p2 → p1) ∧ (p4 → p3)) → (p1 ∨ (p2 → p1))) ∧ (p3 ∨ False)) → (((((p1 → p5) ∧ p3) ∨ p4) ∨ (True ∨ p3)) ∨ (True ∧ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
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
theorem thm_5_vars_165301828566250848953492603157 : ((((p4 ∨ p5) → (((p5 → p4) ∨ ((False → p5) ∨ (p3 ∧ p5))) ∧ True)) → (p2 ∧ p4)) ∨ ((False ∧ p4) → ((p4 → (p5 → p5)) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63413865822936821496639290326 : ((p5 ∧ (p5 ∨ ((p4 ∨ (((False ∨ p4) → p1) → False)) ∨ (True → (p4 ∧ (((p5 ∨ (p3 ∨ p2)) ∨ p3) ∨ ((p5 ∨ True) ∧ p1))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_91102246580235124633182938706 : (((p3 → p4) ∧ (True ∧ ((p4 → (True → p5)) ∧ (p5 ∧ (False ∨ (((p4 ∨ (p4 ∨ p5)) → p1) → (p1 → (p4 ∧ (p2 ∧ p1))))))))) → p5) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165902276161625010520829924175 : (((p1 ∨ (p4 ∨ False)) → (((p1 ∧ ((p1 → p3) → p1)) ∧ p3) ∨ (p4 ∨ (p1 ∨ p4)))) ∨ (((False ∧ False) ∧ False) ∧ (p2 ∧ (True ∨ False)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- False on the left can always be used.
      apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119521258917224122703573870279 : ((p5 → (((p3 → (((((True ∨ p5) ∧ False) → p3) → p3) ∧ (p1 ∨ p3))) → (p4 ∧ (((True ∨ p4) ∨ p4) → p1))) ∨ p5)) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64349985880896093671082410696 : ((p1 ∨ ((((p3 ∨ ((((p1 ∨ (p1 → (p4 ∧ p4))) → (p3 ∧ True)) → ((True ∧ (p3 ∨ p3)) ∧ p1)) ∧ p2)) → p5) ∨ True) ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140657103548769229077820841278 : ((((p2 ∧ (False ∧ ((True → (p4 → p1)) → p5))) → ((False ∧ p5) ∨ p5)) ∧ ((False ∨ (p3 ∧ (True → True))) ∧ p4)) → (False ∨ (p1 ∨ True))) := by
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
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_91229975310344941526470289782 : (((False ∧ True) ∨ (((True → False) ∨ ((True ∨ (((p4 ∨ True) ∨ (p1 ∨ p4)) ∨ True)) ∨ p4)) ∧ ((p5 ∨ ((p2 → p2) ∨ p5)) → False))) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h9 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h10 := h8 h9
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
          have h14 : (p5 ∨ ((p2 → p2) ∨ p5)) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Implications on the right can always be decomposed.
            intro h15
            -- One of the premise coincides with the conclusion.
            exact h15
          -- We have shown the premise of h7, we can now drive its conclusion.
          let h16 := h7 h14
          -- False on the left can always be used.
          apply False.elim h16
        case inr h17 =>
          -- Disjunctions on the left can always be decomposed.
          cases h17
          case inl h18 =>
            -- Disjunctions on the left can always be decomposed.
            cases h18
            case inl h19 =>
              -- Disjunctions on the left can always be decomposed.
              cases h19
              case inl h20 =>
                -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
                have h21 : (p5 ∨ ((p2 → p2) ∨ p5)) := by
                  -- Show the right disjunct based on <expert-advice>.
                  apply Or.inr
                  -- Show the left disjunct based on <expert-advice>.
                  apply Or.inl
                  -- Implications on the right can always be decomposed.
                  intro h22
                  -- One of the premise coincides with the conclusion.
                  exact h22
                -- We have shown the premise of h7, we can now drive its conclusion.
                let h23 := h7 h21
                -- False on the left can always be used.
                apply False.elim h23
              case inr h24 =>
                -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
                have h25 : (p5 ∨ ((p2 → p2) ∨ p5)) := by
                  -- Show the right disjunct based on <expert-advice>.
                  apply Or.inr
                  -- Show the left disjunct based on <expert-advice>.
                  apply Or.inl
                  -- Implications on the right can always be decomposed.
                  intro h26
                  -- One of the premise coincides with the conclusion.
                  exact h26
                -- We have shown the premise of h7, we can now drive its conclusion.
                let h27 := h7 h25
                -- False on the left can always be used.
                apply False.elim h27
            case inr h28 =>
              -- Disjunctions on the left can always be decomposed.
              cases h28
              case inl h29 =>
                -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
                have h30 : (p5 ∨ ((p2 → p2) ∨ p5)) := by
                  -- Show the right disjunct based on <expert-advice>.
                  apply Or.inr
                  -- Show the left disjunct based on <expert-advice>.
                  apply Or.inl
                  -- Implications on the right can always be decomposed.
                  intro h31
                  -- One of the premise coincides with the conclusion.
                  exact h31
                -- We have shown the premise of h7, we can now drive its conclusion.
                let h32 := h7 h30
                -- False on the left can always be used.
                apply False.elim h32
              case inr h33 =>
                -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
                have h34 : (p5 ∨ ((p2 → p2) ∨ p5)) := by
                  -- Show the right disjunct based on <expert-advice>.
                  apply Or.inr
                  -- Show the left disjunct based on <expert-advice>.
                  apply Or.inl
                  -- Implications on the right can always be decomposed.
                  intro h35
                  -- One of the premise coincides with the conclusion.
                  exact h35
                -- We have shown the premise of h7, we can now drive its conclusion.
                let h36 := h7 h34
                -- False on the left can always be used.
                apply False.elim h36
          case inr h37 =>
            -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
            have h38 : (p5 ∨ ((p2 → p2) ∨ p5)) := by
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- Implications on the right can always be decomposed.
              intro h39
              -- One of the premise coincides with the conclusion.
              exact h39
            -- We have shown the premise of h7, we can now drive its conclusion.
            let h40 := h7 h38
            -- False on the left can always be used.
            apply False.elim h40
      case inr h41 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h42 : (p5 ∨ ((p2 → p2) ∨ p5)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h43
          -- One of the premise coincides with the conclusion.
          exact h43
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h44 := h7 h42
        -- False on the left can always be used.
        apply False.elim h44



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347779419112417013963192867447 : (p3 → (((p3 → p2) → False) ∨ (((p4 → ((p2 → True) ∨ ((p1 ∨ (((p1 → p1) ∧ True) → p4)) ∨ (p4 → p2)))) → p4) ∨ (p5 ∨ True)))) := by
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
theorem thm_5_vars_18742947202748289076992005010 : ((((p4 ∧ (True ∧ ((p4 → (False ∨ p2)) ∨ ((p3 ∨ p5) ∧ ((p2 → True) ∨ p5))))) ∧ p5) ∨ (False → ((p3 → (False ∨ True)) → p5))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_149579013463100975205022522875 : ((p3 ∧ ((((p3 ∨ (p1 → p1)) → (p3 → (((p2 ∨ p2) ∨ (p4 → (p4 ∨ p3))) ∧ True))) ∨ p5) ∧ p1)) ∨ ((False ∨ (p2 → p2)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614869233084729572343023729120 : (((((p4 → ((True → False) ∧ (p1 ∨ (True → ((p2 ∨ (((p5 ∨ p1) ∨ p2) ∨ p3)) ∨ False))))) ∨ (((p3 → False) → p4) ∧ False)) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165246885208391741482893579988 : (((p3 ∨ ((p4 ∨ False) ∧ (((p4 ∨ p3) → p5) ∧ ((p5 ∨ p2) ∧ p4)))) ∨ (False ∧ p2)) ∨ (True ∨ ((True ∨ ((False ∧ True) → p4)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139836936653489391152247146000 : (((p2 → ((False ∨ ((p3 ∨ p2) → False)) → ((p1 → p3) ∧ (p4 ∧ ((p4 ∧ ((p5 → False) → p5)) → p2))))) → False) → ((p3 ∨ p4) → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h4 : (p2 → ((False ∨ ((p3 ∨ p2) → False)) → ((p1 → p3) ∧ (p4 ∧ ((p4 ∧ ((p5 → False) → p5)) → p2))))) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h7
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- False on the left can always be used.
        apply False.elim h8
      case inr h9 =>
        -- One of the premise coincides with the conclusion.
        exact h3
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h10 =>
        -- False on the left can always be used.
        apply False.elim h10
      case inr h11 =>
        -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
        have h12 : (p3 ∨ p2) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h3
        -- We have shown the premise of h11, we can now drive its conclusion.
        let h13 := h11 h12
        -- False on the left can always be used.
        apply False.elim h13
      -- Implications on the right can always be decomposed.
      intro h14
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h17 =>
        -- False on the left can always be used.
        apply False.elim h17
      case inr h18 =>
        -- One of the premise coincides with the conclusion.
        exact h5
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h19 := h1 h4
    -- False on the left can always be used.
    apply False.elim h19
  case inr h20 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h21 : (p2 → ((False ∨ ((p3 ∨ p2) → False)) → ((p1 → p3) ∧ (p4 ∧ ((p4 ∧ ((p5 → False) → p5)) → p2))))) := by
      -- Implications on the right can always be decomposed.
      intro h22
      -- Implications on the right can always be decomposed.
      intro h23
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h24
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h25 =>
        -- False on the left can always be used.
        apply False.elim h25
      case inr h26 =>
        -- We want to use the implication h26 based on <expert-advice>. So we show its premise.
        have h27 : (p3 ∨ p2) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h22
        -- We have shown the premise of h26, we can now drive its conclusion.
        let h28 := h26 h27
        -- False on the left can always be used.
        apply False.elim h28
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h29 =>
        -- False on the left can always be used.
        apply False.elim h29
      case inr h30 =>
        -- One of the premise coincides with the conclusion.
        exact h20
      -- Implications on the right can always be decomposed.
      intro h31
      -- Conjunctions on the left can always be decomposed.
      let h32 := h31.left
      let h33 := h31.right
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h34 =>
        -- False on the left can always be used.
        apply False.elim h34
      case inr h35 =>
        -- One of the premise coincides with the conclusion.
        exact h22
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h36 := h1 h21
    -- False on the left can always be used.
    apply False.elim h36



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41429033335210594147312723668 : (((((((p5 ∨ ((p2 → (p1 ∨ True)) ∨ p1)) ∧ (p1 → p2)) ∨ p1) → p2) → ((p1 ∧ ((p4 ∧ (p5 ∨ p3)) ∨ p4)) ∨ p5)) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41938585935697149666953656105 : ((((p5 → (p3 ∧ p4)) → (p5 ∨ (((p2 ∨ ((True ∧ ((p2 ∨ p4) → False)) → p4)) → ((False → p4) → p3)) ∨ (False → p5)))) ∨ p1) ∨ False) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149689554061013480054894485244 : ((p5 ∧ ((p3 ∧ ((p4 ∨ ((False ∧ p5) ∧ p3)) ∧ (p3 ∨ (p4 ∧ (p2 ∨ p5))))) ∧ (p1 ∧ (False ∨ False)))) ∨ (True ∨ ((p5 ∧ False) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59521319557544465063749431769 : (((p2 → p3) ∨ (((((p5 → p2) → (True → True)) → p3) ∨ p2) ∧ ((p4 ∧ p3) ∨ (p2 ∨ ((True ∨ ((p1 ∧ True) ∧ p1)) ∨ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_382687666801440957954348135099 : ((((((p5 ∨ (p4 → p3)) ∧ (False ∨ ((((((p3 ∧ (p4 ∨ (p3 → p3))) ∧ p4) → p4) ∧ (True ∧ p2)) → p2) → False))) ∨ True) ∨ False) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321049768732988067630968412078 : (p4 ∨ (p1 ∨ ((((p2 → (p1 ∨ (True → p5))) ∨ ((p3 ∨ (((p3 ∨ False) → (True ∧ p1)) → (p5 ∨ p4))) ∨ p4)) ∧ (p2 → p5)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50606092689967012784788813737 : ((((p3 ∨ (p4 → (p4 ∧ ((((p5 ∨ p4) → False) → False) ∨ (p2 ∨ (p5 ∧ False)))))) ∨ (False → p2)) → (((p3 → p5) ∧ p4) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249102441091797545882023006634 : ((p4 ∨ p2) ∨ (((True → ((((False → (p3 ∨ ((False ∨ p2) → True))) ∨ True) → ((p3 → (p2 ∧ p5)) → p1)) ∧ p4)) ∨ (p2 ∨ True)) ∧ True)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4131711954769817975650443021 : (p3 ∨ (p5 ∨ (((p5 → ((True ∨ p2) ∧ ((p2 ∨ p5) → True))) → (p4 ∧ ((p2 ∧ p1) ∨ (p3 → ((True → True) ∧ p5))))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_243005824874071736594305554246 : ((p4 → True) ∧ ((p3 ∨ (p5 ∨ p4)) → (p5 → ((p3 ∧ ((p1 ∨ (p5 → (p5 ∧ (p3 ∨ (p3 ∧ p4))))) ∨ p4)) ∨ ((p4 → False) → p5))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192335149101256650462639226617 : (((p1 ∨ (False → (True → (True ∧ (p1 ∧ p3))))) ∧ p5) → ((p2 ∧ (p3 ∨ ((p4 ∨ p3) ∨ (False → p2)))) → (p3 ∨ ((p3 ∧ False) ∨ True)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h1.left
    let h7 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h1.left
        let h14 := h1.right
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h16 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h1.left
        let h19 := h1.right
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h21 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h1.left
      let h24 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h25 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h26 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204558914716115513743021368972 : ((((p5 → (p2 ∨ p3)) → p5) ∨ p2) ∨ (p2 ∨ (((((False ∨ p3) ∨ (p2 ∨ p4)) ∧ (p2 → ((False → p5) ∨ p3))) → (True ∨ p1)) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    cases h4
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



