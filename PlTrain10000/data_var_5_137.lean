variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61243529202129057283224949252 : ((False ∧ (p4 ∧ (((p5 ∨ (p2 ∧ p2)) ∧ p1) → (((((((p2 ∨ False) → p4) ∨ ((p4 → p1) ∧ p5)) ∧ p5) → p2) → p5) ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_696116669074384934738860100715 : ((((True ∨ (((p4 → p3) ∨ True) ∧ ((True → ((p1 ∨ p1) ∧ p1)) ∨ p5))) → (((False ∨ p1) ∨ (p1 ∧ (p3 ∨ (p3 ∨ p5)))) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_639205358940407227438940963311 : (((((p5 ∨ (False ∨ (p2 ∧ True))) ∨ ((((p4 ∨ p1) ∧ (((False ∨ (p3 → p3)) ∧ True) ∧ p4)) → p4) → ((True → p1) ∨ True))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312008535740082702036911863018 : (p2 ∨ (p4 ∨ ((((p1 ∨ ((p4 ∨ p2) → (p3 ∨ p5))) → (False ∧ p5)) ∧ p1) → (p2 ∨ (((False ∧ (p2 ∧ (p3 ∨ p5))) ∨ p4) ∧ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p1 ∨ ((p4 ∨ p2) → (p3 ∨ p5))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138891878026244325183764244103 : (((True → (((p3 ∧ ((False → p4) ∧ (p5 → p5))) ∨ p4) ∧ (p5 ∧ ((False ∨ (p4 ∧ (p1 ∧ p2))) ∧ p4)))) ∧ p3) → ((False ∨ p4) ∧ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h8
  -- Conjunctions on the left can always be decomposed.
  let h9 := h1.left
  let h10 := h1.right
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h11 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h12 := h9 h11
  -- We need to get the right conjuct of h12 based on <expert-advice>.
  let h13 := h12.right
  -- We need to get the right conjuct of h13 based on <expert-advice>.
  let h14 := h13.right
  -- We need to get the left conjuct of h14 based on <expert-advice>.
  let h15 := h14.left
  -- Disjunctions on the left can always be decomposed.
  cases h15
  case inl h16 =>
    -- False on the left can always be used.
    apply False.elim h16
  case inr h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- Conjunctions on the left can always be decomposed.
    let h20 := h19.left
    let h21 := h19.right
    -- One of the premise coincides with the conclusion.
    exact h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115732058310545339908249484091 : (((((p4 ∨ True) ∨ p2) ∨ (p5 → p4)) → ((p3 ∨ p5) ∨ ((p1 ∧ (p4 ∧ (p3 ∨ ((p1 ∧ (p3 → p4)) ∧ p2)))) → p4))) ∨ (p4 ∧ p2)) := by
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
        -- Implications on the right can always be decomposed.
        intro h5
        -- Conjunctions on the left can always be decomposed.
        let h6 := h5.left
        let h7 := h5.right
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- One of the premise coincides with the conclusion.
          exact h8
        case inr h11 =>
          -- Conjunctions on the left can always be decomposed.
          let h12 := h11.left
          let h13 := h11.right
          -- Conjunctions on the left can always be decomposed.
          let h14 := h12.left
          let h15 := h12.right
          -- One of the premise coincides with the conclusion.
          exact h8
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h17
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- Conjunctions on the left can always be decomposed.
        let h20 := h19.left
        let h21 := h19.right
        -- Disjunctions on the left can always be decomposed.
        cases h21
        case inl h22 =>
          -- One of the premise coincides with the conclusion.
          exact h20
        case inr h23 =>
          -- Conjunctions on the left can always be decomposed.
          let h24 := h23.left
          let h25 := h23.right
          -- Conjunctions on the left can always be decomposed.
          let h26 := h24.left
          let h27 := h24.right
          -- One of the premise coincides with the conclusion.
          exact h20
    case inr h28 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h29
      -- Conjunctions on the left can always be decomposed.
      let h30 := h29.left
      let h31 := h29.right
      -- Conjunctions on the left can always be decomposed.
      let h32 := h31.left
      let h33 := h31.right
      -- Disjunctions on the left can always be decomposed.
      cases h33
      case inl h34 =>
        -- One of the premise coincides with the conclusion.
        exact h32
      case inr h35 =>
        -- Conjunctions on the left can always be decomposed.
        let h36 := h35.left
        let h37 := h35.right
        -- Conjunctions on the left can always be decomposed.
        let h38 := h36.left
        let h39 := h36.right
        -- One of the premise coincides with the conclusion.
        exact h32
  case inr h40 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h41
    -- Conjunctions on the left can always be decomposed.
    let h42 := h41.left
    let h43 := h41.right
    -- Conjunctions on the left can always be decomposed.
    let h44 := h43.left
    let h45 := h43.right
    -- Disjunctions on the left can always be decomposed.
    cases h45
    case inl h46 =>
      -- One of the premise coincides with the conclusion.
      exact h44
    case inr h47 =>
      -- Conjunctions on the left can always be decomposed.
      let h48 := h47.left
      let h49 := h47.right
      -- Conjunctions on the left can always be decomposed.
      let h50 := h48.left
      let h51 := h48.right
      -- One of the premise coincides with the conclusion.
      exact h44



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_541115851483069354389778999 : (((((p1 ∧ p2) ∧ (False ∨ ((p2 ∨ p5) ∨ ((((p5 ∧ (p5 ∧ True)) ∧ p5) → False) → p5)))) ∨ ((True → p1) ∨ True)) ∨ p1) ∨ p5) := by
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
theorem thm_5_vars_166563579810189073041384747087 : ((p5 ∨ (p3 ∨ (((((True ∧ p3) ∨ (p5 ∨ p2)) ∧ ((False ∨ p3) ∧ True)) ∧ p5) ∨ p4))) ∨ (True ∨ ((((p1 ∧ False) ∨ p4) → p2) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_561840758487315541462258695434 : (((p5 ∨ ((((p2 ∧ (((False ∧ p3) ∨ (p4 → p5)) ∧ (p5 → (((False → False) ∨ (p1 ∧ p5)) → p4)))) → p3) ∨ (p4 → True)) ∨ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_172524598189427040552621734500 : (((p5 ∧ (p4 ∨ False)) ∧ (p2 → ((((False ∨ p3) → p3) ∨ False) ∧ (p3 → p1)))) ∨ (((p5 ∨ ((True ∧ False) ∧ False)) ∨ (False ∧ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258356996475746731934377660369 : ((p5 ∨ False) → ((p2 → ((p3 ∨ (p2 → (p4 ∨ (((p1 ∨ False) ∨ (p2 → (p4 ∨ p3))) ∨ p5)))) ∨ p1)) ∨ (False → (p1 ∧ (p4 → p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241318847193013360183704703852 : ((False → True) ∧ (p2 ∨ ((False ∨ (p4 ∨ p5)) ∨ ((p4 → p5) ∨ (True ∨ ((p3 ∧ p5) ∧ ((p5 ∨ ((p5 ∧ (p3 ∨ p2)) ∨ p3)) ∧ p5))))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_136483313884836124650735775988 : ((((p3 ∨ p1) ∨ True) ∧ ((p1 → (p3 ∨ (p1 ∨ (p3 ∨ ((p4 → (p3 → p3)) → (p5 ∧ (p2 → True))))))) → p4)) ∨ (p3 ∨ (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69343764089375682553616397936 : ((p5 → (p1 ∨ ((p4 ∨ p2) → (p5 → (((True ∨ ((((p5 ∨ p3) ∨ p2) → ((p1 ∧ (p5 ∨ p5)) ∨ p5)) ∧ p4)) → False) ∨ True))))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258341583535279996993178914403 : ((p5 ∨ False) → ((p4 ∧ ((p4 ∨ (p2 ∨ (p3 ∨ (p1 → False)))) ∨ (p4 ∧ ((True → p5) → (((p3 ∨ False) ∧ (p4 → p3)) ∨ p4))))) ∨ True)) := by
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
theorem thm_5_vars_729682592015481386655537309502 : (((((p1 → False) ∨ p4) → (((((p3 ∧ True) ∧ ((p1 ∧ (p4 ∧ p2)) ∨ p3)) ∧ p2) ∧ (True ∧ p2)) ∧ ((p3 ∨ p5) ∨ (False ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172506681814143034274222115320 : ((((p2 ∧ p2) ∨ p4) ∧ ((((p3 → (True ∨ True)) ∧ (p4 ∧ p3)) ∨ p5) ∨ False)) ∨ (True ∧ (p2 → ((False → p5) ∨ ((p5 ∧ False) ∧ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_804222377955824642889133537821 : (((p3 → (((((True ∧ ((p4 → p1) ∧ p4)) ∧ (p4 → ((p2 → p2) → True))) ∧ p2) ∨ False) → (p5 → (p2 → ((p1 ∧ p4) → False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41866965589820634632930208179 : (((((True ∧ p4) → False) ∨ (((p3 ∨ p4) → (((p4 ∨ False) ∨ (p3 ∨ p3)) → p2)) ∨ (p3 ∨ (p2 ∨ ((False ∧ p4) ∨ p3))))) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_83997638740662119756769706293 : (((((p1 ∨ (True → (p4 ∨ (p4 → ((p4 ∨ (p4 → p2)) ∧ p4))))) → p2) ∨ p2) ∧ ((p4 ∨ (p4 ∧ True)) → ((p3 ∨ False) → p1))) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : (p1 ∨ (True → (p4 ∨ (p4 → ((p4 ∨ (p4 → p2)) ∧ p4))))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h8 := h4 h5
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_942413621633044446325403175240 : (((((p5 ∧ (p4 → p2)) ∨ p3) ∧ (((((p2 → (p2 → p5)) ∨ False) ∧ p1) ∨ ((((p3 → p2) → p3) ∨ p4) ∨ p4)) ∧ (True → False))) → p1) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h3.left
    let h8 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h12 =>
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h13 =>
        -- False on the left can always be used.
        apply False.elim h13
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h16 =>
          -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
          have h17 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h8, we can now drive its conclusion.
          let h18 := h8 h17
          -- False on the left can always be used.
          apply False.elim h18
        case inr h19 =>
          -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
          have h20 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h8, we can now drive its conclusion.
          let h21 := h8 h20
          -- False on the left can always be used.
          apply False.elim h21
      case inr h22 =>
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h23 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h24 := h8 h23
        -- False on the left can always be used.
        apply False.elim h24
  case inr h25 =>
    -- Conjunctions on the left can always be decomposed.
    let h26 := h3.left
    let h27 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h26
    case inl h28 =>
      -- Conjunctions on the left can always be decomposed.
      let h29 := h28.left
      let h30 := h28.right
      -- Disjunctions on the left can always be decomposed.
      cases h29
      case inl h31 =>
        -- One of the premise coincides with the conclusion.
        exact h30
      case inr h32 =>
        -- False on the left can always be used.
        apply False.elim h32
    case inr h33 =>
      -- Disjunctions on the left can always be decomposed.
      cases h33
      case inl h34 =>
        -- Disjunctions on the left can always be decomposed.
        cases h34
        case inl h35 =>
          -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
          have h36 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h27, we can now drive its conclusion.
          let h37 := h27 h36
          -- False on the left can always be used.
          apply False.elim h37
        case inr h38 =>
          -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
          have h39 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h27, we can now drive its conclusion.
          let h40 := h27 h39
          -- False on the left can always be used.
          apply False.elim h40
      case inr h41 =>
        -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
        have h42 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h27, we can now drive its conclusion.
        let h43 := h27 h42
        -- False on the left can always be used.
        apply False.elim h43
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213714129251910337764519773873 : ((((True ∨ p5) → p4) ∨ p4) ∨ ((((((p1 → p2) ∨ p2) ∧ p3) ∨ (True → (p1 ∨ (p3 ∧ p1)))) ∧ (p4 ∧ p3)) ∨ (p2 ∨ (True ∨ p2)))) := by
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
theorem thm_5_vars_244879276475101795094156894641 : ((p1 ∧ p2) ∨ (((p4 ∨ True) ∧ ((p1 → (p5 → (p3 → (p3 ∧ False)))) ∨ p5)) ∨ ((p3 ∧ (p5 ∧ (True ∧ p5))) ∨ ((p1 ∨ True) ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_586344081857172472398936332472 : ((((((((p4 ∨ p4) ∨ p5) → (p3 ∧ p2)) ∨ (((((p2 → (True → p2)) ∧ (False ∧ p3)) → p3) → (p4 → p5)) ∧ p4)) ∧ p3) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245680960286495886865454614657 : ((p3 ∧ p1) ∨ ((p1 → p4) ∨ (((True ∨ (p2 → (p3 → p3))) ∧ (((p4 ∧ True) → True) → (((p5 ∧ False) ∨ False) ∧ p2))) → (p3 ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : ((p4 ∧ True) → True) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h7 := h3 h5
    -- We need to get the left conjuct of h7 based on <expert-advice>.
    let h8 := h7.left
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h14 : ((p4 ∧ True) → True) := by
      -- Implications on the right can always be decomposed.
      intro h15
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h16 := h3 h14
    -- We need to get the left conjuct of h16 based on <expert-advice>.
    let h17 := h16.left
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- False on the left can always be used.
      apply False.elim h20
    case inr h21 =>
      -- False on the left can always be used.
      apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192946050945041243640361821153 : ((((p1 → p4) ∧ (p3 ∨ (p4 ∨ True))) ∨ (False ∨ p5)) → ((((p5 ∧ True) ∧ p4) ∨ ((p5 ∧ p2) ∧ p2)) → (p1 ∨ (True ∨ (True ∨ False))))) := by
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
    cases h1
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- False on the left can always be used.
        apply False.elim h16
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
    -- Conjunctions on the left can always be decomposed.
    let h21 := h19.left
    let h22 := h19.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h23 =>
      -- Conjunctions on the left can always be decomposed.
      let h24 := h23.left
      let h25 := h23.right
      -- Disjunctions on the left can always be decomposed.
      cases h25
      case inl h26 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h27 =>
        -- Disjunctions on the left can always be decomposed.
        cases h27
        case inl h28 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h29 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h30 =>
      -- Disjunctions on the left can always be decomposed.
      cases h30
      case inl h31 =>
        -- False on the left can always be used.
        apply False.elim h31
      case inr h32 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157051151020631681179125492128 : (((p2 ∧ ((((p4 → p5) ∧ (p2 → p3)) ∨ (p4 ∧ ((p2 ∨ p5) → True))) → (p4 ∧ p3))) ∨ True) ∨ (((False → (True ∧ False)) ∧ p1) ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68193892160613261225501601114 : ((p3 → (((((p1 ∨ p5) ∨ True) ∧ p2) ∨ (False ∧ (((((p1 → (p2 ∧ p5)) ∧ False) ∧ (p5 ∨ False)) ∧ True) ∧ (p4 ∧ True)))) ∨ p3)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309838711768797375158001853920 : (p2 ∨ ((((((p1 ∧ (p3 ∨ p4)) ∨ p1) ∧ (p3 → p5)) ∧ ((True ∨ (False ∨ False)) ∨ p2)) ∨ (p5 ∨ p5)) → (p1 ∨ (False ∨ (True ∨ p3))))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
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
        cases h4
        case inl h11 =>
          -- Disjunctions on the left can always be decomposed.
          cases h11
          case inl h12 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h8
          case inr h13 =>
            -- Disjunctions on the left can always be decomposed.
            cases h13
            case inl h14 =>
              -- False on the left can always be used.
              apply False.elim h14
            case inr h15 =>
              -- False on the left can always be used.
              apply False.elim h15
        case inr h16 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h8
      case inr h17 =>
        -- Disjunctions on the left can always be decomposed.
        cases h4
        case inl h18 =>
          -- Disjunctions on the left can always be decomposed.
          cases h18
          case inl h19 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h8
          case inr h20 =>
            -- Disjunctions on the left can always be decomposed.
            cases h20
            case inl h21 =>
              -- False on the left can always be used.
              apply False.elim h21
            case inr h22 =>
              -- False on the left can always be used.
              apply False.elim h22
        case inr h23 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h8
    case inr h24 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h25 =>
        -- Disjunctions on the left can always be decomposed.
        cases h25
        case inl h26 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h24
        case inr h27 =>
          -- Disjunctions on the left can always be decomposed.
          cases h27
          case inl h28 =>
            -- False on the left can always be used.
            apply False.elim h28
          case inr h29 =>
            -- False on the left can always be used.
            apply False.elim h29
      case inr h30 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h24
  case inr h31 =>
    -- Disjunctions on the left can always be decomposed.
    cases h31
    case inl h32 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h33 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326357922885674583909960576439 : (p5 ∨ (p5 → ((((False ∨ p5) ∧ (((p3 ∨ ((p1 ∨ p3) ∧ (True ∨ p2))) → True) → (False ∨ p1))) ∨ True) ∧ (p5 → (True ∧ (p1 ∨ p5)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248838566560596493487589621615 : ((p3 ∨ p4) ∨ ((p4 ∨ False) ∨ (p2 ∨ ((((False ∨ p2) → (p3 ∨ True)) ∨ (True → ((p1 → True) → (p4 ∧ p4)))) ∧ (True ∧ (p2 → p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- True on the right can always be proven directly.
    apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201295907145999294608726551882 : ((p4 → ((p5 ∧ (p3 ∧ p4)) ∨ (p2 ∨ p5))) → ((True ∨ ((p3 ∨ p2) ∧ (p2 ∨ p2))) → (p3 ∨ (True ∧ ((p4 ∨ p2) ∨ (p1 ∨ True)))))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h7
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h11 =>
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
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h12 =>
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
        -- One of the premise coincides with the conclusion.
        exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192073175496768515347877124208 : ((p3 → (False ∧ (p1 → (((p4 ∧ p4) ∧ p1) ∨ p5)))) ∨ ((p2 ∨ (False ∨ (p1 → ((p1 ∧ (True → True)) → p1)))) ∨ ((True → p3) → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_799256258471433371578684293082 : (((p1 → (p3 ∧ (((False ∧ ((p4 ∨ p5) ∨ (p1 ∧ ((True → p5) ∨ (p4 → (False ∧ (p5 → p5))))))) ∧ p1) ∧ ((p1 → p2) → p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322441773880920871963788039221 : (p5 ∨ (((p1 ∨ (p5 ∨ (p1 ∨ True))) ∧ (((True → False) ∨ True) ∨ ((p1 → True) ∧ (p4 → (p5 ∨ ((False → (p1 ∧ True)) ∨ p2)))))) ∨ p1)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52948285448755226903013630916 : ((((((p1 → p2) ∨ ((True ∨ p2) → False)) ∨ (True ∨ p5)) ∨ p1) ∧ (p5 → ((p1 ∧ ((True ∨ (p3 ∧ p3)) → p3)) ∨ (True ∧ p5)))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149643052515861248752666925236 : ((p4 ∧ (((((p2 ∨ p2) ∨ p3) ∧ ((p2 ∨ p1) ∨ (p4 ∨ (p1 ∨ False)))) ∧ False) ∨ ((True ∧ p1) ∧ p5))) ∨ ((False ∨ True) → (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_163134472501927918212256833088 : ((((p4 → ((True → p5) ∨ True)) → ((p5 ∨ False) ∨ p4)) ∨ (((True → p2) → True) ∨ False)) ∧ (((p2 ∨ (True → (p4 ∧ p1))) ∧ False) → p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337358108995333067368948551078 : (p1 → (((p3 ∨ ((p1 ∧ (p3 ∨ p5)) ∧ ((((p3 ∨ p4) ∨ p2) ∨ ((True ∨ p4) → p2)) ∧ p3))) ∨ (p5 ∨ p3)) ∨ (p3 → (p2 → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683198630442650325199845593 : (((p5 ∧ (p5 ∨ ((p2 → p4) → (((p2 → (True ∧ False)) → False) ∨ True)))) ∧ ((((True ∧ True) ∨ p3) ∧ (p5 ∨ False)) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164379575398304134051475470313 : ((p4 → (((((((False → p3) ∧ p2) ∨ True) → (False → p5)) ∨ (False ∨ True)) → p2) ∨ p4)) ∧ (False → ((p2 → p2) ∨ (p2 → (p5 → p1))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301444610485513835852662793899 : (False ∨ ((p5 ∨ (p1 ∨ (p2 ∧ p4))) → ((p2 ∨ (p2 ∨ (p2 ∨ False))) → ((p4 ∧ (p2 → False)) → (((p1 ∧ p2) → p4) → (p1 ∧ p3)))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h8 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h9 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h10 := h6 h9
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h16 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h14
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h17 := h6 h16
        -- False on the left can always be used.
        apply False.elim h17
  case inr h18 =>
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h19 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h20 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h21 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h19
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h22 := h6 h21
        -- False on the left can always be used.
        apply False.elim h22
      case inr h23 =>
        -- Disjunctions on the left can always be decomposed.
        cases h23
        case inl h24 =>
          -- One of the premise coincides with the conclusion.
          exact h24
        case inr h25 =>
          -- Conjunctions on the left can always be decomposed.
          let h26 := h25.left
          let h27 := h25.right
          -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
          have h28 : p2 := by
            -- One of the premise coincides with the conclusion.
            exact h26
          -- We have shown the premise of h6, we can now drive its conclusion.
          let h29 := h6 h28
          -- False on the left can always be used.
          apply False.elim h29
    case inr h30 =>
      -- Disjunctions on the left can always be decomposed.
      cases h30
      case inl h31 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h32 =>
          -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
          have h33 : p2 := by
            -- One of the premise coincides with the conclusion.
            exact h31
          -- We have shown the premise of h6, we can now drive its conclusion.
          let h34 := h6 h33
          -- False on the left can always be used.
          apply False.elim h34
        case inr h35 =>
          -- Disjunctions on the left can always be decomposed.
          cases h35
          case inl h36 =>
            -- One of the premise coincides with the conclusion.
            exact h36
          case inr h37 =>
            -- Conjunctions on the left can always be decomposed.
            let h38 := h37.left
            let h39 := h37.right
            -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
            have h40 : p2 := by
              -- One of the premise coincides with the conclusion.
              exact h38
            -- We have shown the premise of h6, we can now drive its conclusion.
            let h41 := h6 h40
            -- False on the left can always be used.
            apply False.elim h41
      case inr h42 =>
        -- False on the left can always be used.
        apply False.elim h42
  -- Conjunctions on the left can always be decomposed.
  let h43 := h3.left
  let h44 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h45 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h46 =>
      -- We want to use the implication h44 based on <expert-advice>. So we show its premise.
      have h47 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h45
      -- We have shown the premise of h44, we can now drive its conclusion.
      let h48 := h44 h47
      -- False on the left can always be used.
      apply False.elim h48
    case inr h49 =>
      -- Disjunctions on the left can always be decomposed.
      cases h49
      case inl h50 =>
        -- We want to use the implication h44 based on <expert-advice>. So we show its premise.
        have h51 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h45
        -- We have shown the premise of h44, we can now drive its conclusion.
        let h52 := h44 h51
        -- False on the left can always be used.
        apply False.elim h52
      case inr h53 =>
        -- Conjunctions on the left can always be decomposed.
        let h54 := h53.left
        let h55 := h53.right
        -- We want to use the implication h44 based on <expert-advice>. So we show its premise.
        have h56 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h54
        -- We have shown the premise of h44, we can now drive its conclusion.
        let h57 := h44 h56
        -- False on the left can always be used.
        apply False.elim h57
  case inr h58 =>
    -- Disjunctions on the left can always be decomposed.
    cases h58
    case inl h59 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h60 =>
        -- We want to use the implication h44 based on <expert-advice>. So we show its premise.
        have h61 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h59
        -- We have shown the premise of h44, we can now drive its conclusion.
        let h62 := h44 h61
        -- False on the left can always be used.
        apply False.elim h62
      case inr h63 =>
        -- Disjunctions on the left can always be decomposed.
        cases h63
        case inl h64 =>
          -- We want to use the implication h44 based on <expert-advice>. So we show its premise.
          have h65 : p2 := by
            -- One of the premise coincides with the conclusion.
            exact h59
          -- We have shown the premise of h44, we can now drive its conclusion.
          let h66 := h44 h65
          -- False on the left can always be used.
          apply False.elim h66
        case inr h67 =>
          -- Conjunctions on the left can always be decomposed.
          let h68 := h67.left
          let h69 := h67.right
          -- We want to use the implication h44 based on <expert-advice>. So we show its premise.
          have h70 : p2 := by
            -- One of the premise coincides with the conclusion.
            exact h68
          -- We have shown the premise of h44, we can now drive its conclusion.
          let h71 := h44 h70
          -- False on the left can always be used.
          apply False.elim h71
    case inr h72 =>
      -- Disjunctions on the left can always be decomposed.
      cases h72
      case inl h73 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h74 =>
          -- We want to use the implication h44 based on <expert-advice>. So we show its premise.
          have h75 : p2 := by
            -- One of the premise coincides with the conclusion.
            exact h73
          -- We have shown the premise of h44, we can now drive its conclusion.
          let h76 := h44 h75
          -- False on the left can always be used.
          apply False.elim h76
        case inr h77 =>
          -- Disjunctions on the left can always be decomposed.
          cases h77
          case inl h78 =>
            -- We want to use the implication h44 based on <expert-advice>. So we show its premise.
            have h79 : p2 := by
              -- One of the premise coincides with the conclusion.
              exact h73
            -- We have shown the premise of h44, we can now drive its conclusion.
            let h80 := h44 h79
            -- False on the left can always be used.
            apply False.elim h80
          case inr h81 =>
            -- Conjunctions on the left can always be decomposed.
            let h82 := h81.left
            let h83 := h81.right
            -- We want to use the implication h44 based on <expert-advice>. So we show its premise.
            have h84 : p2 := by
              -- One of the premise coincides with the conclusion.
              exact h82
            -- We have shown the premise of h44, we can now drive its conclusion.
            let h85 := h44 h84
            -- False on the left can always be used.
            apply False.elim h85
      case inr h86 =>
        -- False on the left can always be used.
        apply False.elim h86



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_542575206500778715397098041 : (((((p2 ∨ ((p1 ∧ p5) ∧ (p1 ∨ p2))) ∨ ((False ∨ (True ∨ p2)) ∧ (p1 ∨ True))) ∨ (p2 ∧ (p3 → (p2 ∧ p1)))) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_561891209852489258482165637464 : (((p5 ∨ ((((((True → (True ∧ p3)) → p5) ∨ (p5 → p2)) ∧ p4) ∨ (p2 → ((p4 ∨ p5) ∨ (True ∨ ((p4 ∨ p5) → p3))))) ∨ p4)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_802394288610666403307094311453 : (((p2 → (False ∨ (((True ∧ ((p3 ∧ p4) → ((p1 ∧ False) ∧ False))) ∧ (p3 ∧ p5)) → ((p1 ∧ ((p3 → p1) ∧ p5)) ∧ (p4 → True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260362519461500738175602647033 : ((p2 → p5) → (((p3 ∧ ((p1 ∨ (p4 ∧ p5)) ∧ p5)) ∨ (p3 → (False → (True ∨ (False → True))))) ∨ (((True → False) ∧ p3) ∧ (p3 ∨ p3)))) := by
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
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166802990555093695496403740418 : (((((((p1 ∧ p1) ∨ (True ∧ p1)) → (p3 ∨ (p3 ∨ False))) ∨ (p2 → p3)) ∧ p4) ∧ p3) → ((p1 ∨ (p5 ∧ p2)) ∨ (True → (p2 → p2)))) := by
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
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49092349411747495402296743319 : (((((((p4 ∧ p5) ∧ (p1 ∨ False)) ∧ (p1 ∨ (((p1 → p3) ∨ p2) ∧ p4))) ∨ True) ∨ ((p3 ∨ True) ∧ p2)) ∨ (p3 ∧ (False → p2))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245909438132379889612965042214 : ((p3 ∧ p5) ∨ (((p4 ∨ p4) ∧ ((p1 ∧ p1) ∨ (p2 → (p2 ∧ (p5 ∧ (p1 ∧ (True ∨ True))))))) → (False ∨ (p1 ∨ ((p2 → False) → True))))) := by
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
    cases h3
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h15
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133827003579919410106986900967 : ((((p1 → p3) ∨ (((p3 → (p2 → True)) → p2) → ((p4 ∧ (True ∨ p5)) → (p5 → ((p2 ∨ p4) ∧ p4))))) ∧ p1) ∨ (p2 ∨ (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341988160892453515265154527422 : (p2 → ((((p1 ∧ (p3 ∨ (True ∨ True))) ∧ (p4 → (p3 ∨ (p5 ∨ (True → False))))) → (((p4 → False) → p3) → False)) ∨ ((p3 → p2) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42834622367892097289154510742 : (((p1 → (p2 ∨ (p4 ∧ (((p1 ∧ (((p3 ∨ ((p3 ∧ p1) ∧ True)) ∧ True) ∧ ((False ∧ (p1 ∧ False)) → p3))) ∨ p3) ∧ p1)))) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60197286107089076978698962716 : (((p5 ∨ p4) → (True ∧ (((False ∧ (p1 → ((((p5 ∨ p2) ∨ True) ∨ p5) ∧ p2))) → (True ∧ (False ∧ True))) ∧ (False ∧ (p1 ∧ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167139497213442230790128408217 : (((((True ∨ True) → ((p5 ∨ False) ∧ p5)) → ((((False ∧ p1) → p3) ∧ p4) → p2)) ∨ True) → (p4 → (True → (((p3 ∨ p4) → p1) → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h6 : (p3 ∨ p4) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h7 := h4 h6
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h9 : (p3 ∨ p4) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h10 := h4 h9
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680573551494664413178932659754 : (((((((p5 ∨ True) ∨ (p2 → (p1 ∧ False))) → True) ∨ (p1 ∨ (False → ((p2 ∨ (False ∨ p4)) → p1)))) → (((p1 ∧ p4) ∧ p5) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148639900420369816385273996951 : ((((p1 → (p3 ∨ ((True → p3) → p3))) ∧ p5) ∧ (((False ∨ (((False ∧ p3) ∨ p4) ∨ False)) ∧ p5) ∧ p3)) ∨ (p2 → (p4 → (p4 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_335890135369951141181783149011 : (p1 → (((False ∨ ((p4 ∧ p5) → False)) ∨ (((False → ((((False → (p4 → True)) ∨ p3) ∧ (p2 ∧ False)) ∨ (p1 ∨ p2))) → p3) ∨ p1)) ∧ p1)) := by
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
theorem thm_5_vars_44772841156843613102508781891 : ((((False ∧ (p5 ∧ (p5 ∧ p1))) → (((p1 → p4) ∨ (((p3 ∨ p3) ∨ True) ∧ ((((p5 ∨ False) ∨ True) → p3) → False))) ∧ p2)) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601200066171289872543845462174 : ((((p2 ∧ ((True ∧ (p4 ∧ (p2 ∨ ((p4 ∧ p2) ∨ ((p2 ∧ ((p4 ∧ ((p4 ∨ p2) → (p5 → p5))) → True)) ∧ False))))) ∨ p3)) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40764608137561394784776680487 : (((((p1 ∧ False) → ((False ∨ (p5 ∨ ((False → ((False ∧ p5) ∨ (p3 ∨ (p3 → p2)))) ∧ ((p5 ∧ p2) → p1)))) ∨ p4)) → p1) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62889983631568302800874340386 : ((p4 ∧ ((p5 → True) ∧ ((((p1 ∧ (p3 ∧ (False ∨ p1))) ∨ ((p2 ∨ (False ∧ (((p2 ∨ p2) → p5) ∧ p4))) ∧ True)) ∨ True) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58417249623851020606590128711 : (((p2 ∨ p3) ∧ ((p5 ∧ (((p2 ∧ p3) ∨ ((p2 ∨ p1) ∧ (((((p1 ∧ p4) ∧ False) ∧ True) → False) ∨ (True ∧ p5)))) → p3)) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300294660298596287876493812277 : (False ∨ (((((p3 ∧ (((p5 ∧ p2) → p2) ∧ (p2 ∧ p3))) → p5) ∧ ((False ∧ True) ∧ (True ∨ (p3 ∧ p4)))) ∨ True) ∧ ((True ∨ True) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225289813747977827278824772273 : (((False ∨ True) ∧ p4) ∨ ((((((False ∧ (p4 ∨ p3)) ∨ (p1 → ((False → (p1 ∧ p5)) ∧ p3))) ∧ (p3 → p3)) → p4) ∧ True) ∨ (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167989952233558485336841011162 : ((((False → True) → (p5 → (False ∨ p3))) ∧ (False → ((p4 → p4) → ((p2 ∨ p2) ∨ p4)))) → ((((p5 ∧ (p4 ∧ p4)) ∨ p5) ∧ False) ∨ True)) := by
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
theorem thm_5_vars_230490949721628365005492803493 : (((True → False) ∧ p3) → (p5 → (p2 ∧ (p2 ∧ (p3 ∧ (((((False ∨ (p4 ∨ p1)) ∧ True) ∧ (p3 ∧ (p5 ∧ (p2 ∨ p3)))) ∨ p4) ∧ p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h9 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h10 := h7 h9
  -- False on the left can always be used.
  apply False.elim h10
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h11 := h1.left
  let h12 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h12
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h13 := h1.left
  let h14 := h1.right
  -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
  have h15 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h13, we can now drive its conclusion.
  let h16 := h13 h15
  -- False on the left can always be used.
  apply False.elim h16
  -- Conjunctions on the left can always be decomposed.
  let h17 := h1.left
  let h18 := h1.right
  -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
  have h19 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h17, we can now drive its conclusion.
  let h20 := h17 h19
  -- False on the left can always be used.
  apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111517445679906432497651020594 : (((p5 → ((((p3 ∧ p5) ∧ (p1 → p5)) ∧ True) → ((True ∨ ((p1 ∧ p4) ∨ (p2 → (p2 ∨ False)))) ∧ (p1 ∧ p1)))) ∧ p1) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621195560514523949038539709359 : ((((True ∧ (((p3 → (p5 ∨ (False ∧ (((p1 → p3) → ((p1 → False) ∨ (p1 ∧ False))) ∨ False)))) → ((False ∧ p2) ∧ False)) ∨ True)) ∨ p1) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343597590707744256504799584441 : (p2 → ((p3 → p3) → (((((p2 → ((p4 ∨ p5) → p1)) → (p5 ∨ (p3 ∨ (p3 ∨ (p4 ∧ (p2 ∧ p5)))))) ∧ (p1 ∧ p1)) → p3) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64133187054348417531222600624 : ((False ∨ (((p1 ∧ (p5 ∧ True)) → True) → ((((p2 → p5) ∨ True) → p2) → (p5 → ((p3 ∨ (p1 → (False → p1))) → (p2 ∨ p3)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185280455894532436133977869142 : ((p2 ∧ (((p2 ∨ (p2 → p2)) → ((p3 ∨ False) ∨ False)) ∨ p3)) ∨ ((True ∨ p1) ∨ ((p1 ∧ (False → ((p3 → (p3 ∨ p1)) ∨ p2))) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315417202257046758116425239479 : (p3 ∨ (((p1 → p4) → p1) ∨ ((((True ∨ p4) ∧ p1) ∧ p3) → (p3 ∧ (((p2 ∧ True) ∨ (p4 → (p3 ∨ p4))) ∨ (p2 ∧ (p3 → p3))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h12 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h13
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h14 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h15
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209067974385716228188234363794 : ((p1 ∨ (p4 ∧ ((p1 ∨ p4) ∨ p3))) → (((((((((p5 → True) ∨ p1) ∧ p4) → p2) ∧ p2) ∨ ((p3 ∧ p4) ∨ True)) ∨ p2) → p1) ∨ True)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219643095900676087358344162019 : ((False → ((p4 ∨ p5) → True)) → (True ∧ ((((((p2 → ((p1 → (p2 ∧ p5)) ∧ p1)) ∨ p3) → ((p2 ∨ p3) ∧ p1)) ∨ p5) → p5) ∨ True))) := by
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
theorem thm_5_vars_43420601377539633742992838838 : (((((p4 → (p1 ∨ (((p1 ∨ p3) → p5) ∧ False))) → (((p2 ∧ p2) ∨ p3) → (p4 → ((p4 ∧ (True → True)) ∨ False)))) ∨ p2) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51047067852207272637164378103 : (((p2 ∨ ((True → p1) ∧ (p2 → ((((False ∧ p1) ∨ p1) ∨ (p5 ∧ False)) → (False ∧ p2))))) ∧ ((p4 ∧ (p1 → (True ∧ p5))) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157273748532204210496281387813 : ((((p4 → (p1 ∨ p4)) ∨ (((p1 ∨ (p1 ∨ (True → p2))) ∧ (p5 → p5)) ∨ (p2 ∨ p4))) → p1) ∨ (p3 → ((p4 → p4) ∨ (p3 → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657764623474217674576404371814 : ((((True ∧ ((((p3 ∧ (p4 ∧ (p5 ∨ (p3 → p5)))) ∧ p2) ∨ p4) ∧ (p5 → (p5 → (False ∧ ((p3 ∨ p5) → p5)))))) ∨ (True ∨ p5)) ∨ p3) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219077829200291596105044003320 : ((p5 ∧ (p1 → (p4 ∧ p3))) → (p1 ∨ (((((((p4 ∧ p2) ∨ p5) → p2) ∧ p2) ∧ p3) ∨ p5) ∨ ((p4 → (p5 → p1)) → (p2 ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336390883384537850269687373290 : (p1 → ((p2 ∧ ((p2 ∨ (((p4 ∧ ((((p5 ∧ p3) ∧ ((True → p4) ∨ p5)) ∨ p1) ∨ p3)) → True) ∧ ((True → p3) → p5))) → p5)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56968180976854495690529223736 : (((p3 ∨ (True ∨ p3)) ∧ (((((((p3 ∨ False) ∧ True) ∨ (False ∧ p2)) ∨ p5) ∨ False) ∨ (((p3 → (False ∧ p1)) → False) → True)) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_665984928977179183585261907523 : (((((p4 ∧ ((p1 ∨ ((p5 ∨ (((False ∨ False) ∨ p4) ∧ ((p5 → p2) ∧ p4))) ∧ p2)) ∧ (p2 ∧ p2))) → p5) ∧ (p3 ∨ (False ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184406263759571092295580530314 : (((((((p2 ∨ p4) ∧ p3) ∧ p5) ∨ True) ∨ p4) ∧ (p4 → p3)) ∨ ((((p4 → ((p2 → (p3 → p3)) → p3)) ∧ p2) ∧ (p2 ∨ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114982485045015344670927371862 : ((((p3 ∨ (p4 ∨ ((True ∧ p4) → (p1 ∨ (p3 → p1))))) ∨ p1) ∧ (((((False ∧ (p4 ∧ p2)) ∧ True) → p1) ∧ p1) ∧ True)) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134739289610164687525566918033 : ((((True → p5) ∧ (((((False ∧ False) ∧ (p3 ∨ (p1 → (p5 → p3)))) ∨ p4) ∨ (True → (p5 ∧ True))) → False)) → p3) ∨ (p4 ∨ (p4 ∧ p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((((False ∧ False) ∧ (p3 ∨ (p1 → (p5 → p3)))) ∨ p4) ∨ (True → (p5 ∧ True))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h6
    -- One of the premise coincides with the conclusion.
    exact h7
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h8 := h3 h4
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261467729148176587485025416777 : ((p5 → p2) → ((False → (p1 ∨ p1)) → (((False ∨ (True → p5)) ∧ (((((p4 ∨ p3) → p5) ∨ ((True ∧ p5) ∨ False)) ∨ False) ∧ p5)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_736350938984761978261714943137 : ((((False → p5) ∧ ((((((False ∧ p3) ∨ p1) ∨ (p1 ∨ (p5 ∨ p1))) ∧ p2) ∧ (p4 ∧ (p1 ∨ True))) → (((p3 ∨ p4) ∨ p1) ∧ p4))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- False on the left can always be used.
      apply False.elim h9
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h4.left
      let h13 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h14
      case inr h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h11
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h4.left
      let h19 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h20
      case inr h21 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h17
    case inr h22 =>
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h23 =>
        -- Conjunctions on the left can always be decomposed.
        let h24 := h4.left
        let h25 := h4.right
        -- Disjunctions on the left can always be decomposed.
        cases h25
        case inl h26 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h26
        case inr h27 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h24
      case inr h28 =>
        -- Conjunctions on the left can always be decomposed.
        let h29 := h4.left
        let h30 := h4.right
        -- Disjunctions on the left can always be decomposed.
        cases h30
        case inl h31 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h31
        case inr h32 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h28
  -- Conjunctions on the left can always be decomposed.
  let h33 := h2.left
  let h34 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h35 := h33.left
  let h36 := h33.right
  -- Disjunctions on the left can always be decomposed.
  cases h35
  case inl h37 =>
    -- Disjunctions on the left can always be decomposed.
    cases h37
    case inl h38 =>
      -- Conjunctions on the left can always be decomposed.
      let h39 := h38.left
      let h40 := h38.right
      -- False on the left can always be used.
      apply False.elim h39
    case inr h41 =>
      -- Conjunctions on the left can always be decomposed.
      let h42 := h34.left
      let h43 := h34.right
      -- Disjunctions on the left can always be decomposed.
      cases h43
      case inl h44 =>
        -- One of the premise coincides with the conclusion.
        exact h42
      case inr h45 =>
        -- One of the premise coincides with the conclusion.
        exact h42
  case inr h46 =>
    -- Disjunctions on the left can always be decomposed.
    cases h46
    case inl h47 =>
      -- Conjunctions on the left can always be decomposed.
      let h48 := h34.left
      let h49 := h34.right
      -- Disjunctions on the left can always be decomposed.
      cases h49
      case inl h50 =>
        -- One of the premise coincides with the conclusion.
        exact h48
      case inr h51 =>
        -- One of the premise coincides with the conclusion.
        exact h48
    case inr h52 =>
      -- Disjunctions on the left can always be decomposed.
      cases h52
      case inl h53 =>
        -- Conjunctions on the left can always be decomposed.
        let h54 := h34.left
        let h55 := h34.right
        -- Disjunctions on the left can always be decomposed.
        cases h55
        case inl h56 =>
          -- One of the premise coincides with the conclusion.
          exact h54
        case inr h57 =>
          -- One of the premise coincides with the conclusion.
          exact h54
      case inr h58 =>
        -- Conjunctions on the left can always be decomposed.
        let h59 := h34.left
        let h60 := h34.right
        -- Disjunctions on the left can always be decomposed.
        cases h60
        case inl h61 =>
          -- One of the premise coincides with the conclusion.
          exact h59
        case inr h62 =>
          -- One of the premise coincides with the conclusion.
          exact h59
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315792046314506377388184045907 : (p3 ∨ ((p5 ∧ p3) → (((True ∨ (p1 ∧ True)) ∧ (((p5 ∨ (p2 ∧ ((p3 → False) ∨ p5))) → p5) → (p1 ∨ p1))) ∨ ((p4 ∨ p2) → True)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178821472774244833285786256007 : (((p5 ∨ (p3 ∧ p3)) ∨ ((p3 ∨ ((True → p5) ∨ False)) → (p3 ∨ p4))) ∨ (p2 → ((p2 ∧ ((p3 ∧ True) ∨ ((p3 ∧ True) → True))) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330925635613879745180376389597 : (True → (p4 → ((((p5 → p4) → p5) → (p5 ∨ ((False ∨ (p3 → p2)) → p2))) ∨ (((False ∨ (p4 → (p5 → (p5 → p4)))) ∧ p2) → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
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
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137991823696776743979534202505 : ((p5 ∨ (p3 ∧ ((((p2 → (p3 ∨ p3)) → p5) ∧ (p5 → (((p4 ∧ p5) → (True ∧ True)) ∧ p2))) ∨ (p1 ∨ p5)))) ∨ (False → (p4 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44211176334975947666337004239 : ((((p5 ∧ (((p2 ∨ ((((p4 ∧ p4) → p5) ∨ p2) ∨ p1)) → p5) ∨ ((p1 → p3) → p1))) ∧ (True ∨ ((False ∨ p2) → p2))) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160496267551772602372330965951 : ((((((False ∨ p1) ∨ (p3 ∨ p5)) → (p4 ∨ p5)) ∨ (p1 → False)) ∧ ((True → False) ∧ (p5 → True))) → (((p4 ∨ p4) ∨ (False → p5)) ∧ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h7
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h3.left
    let h11 := h3.right
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h12 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h13 := h10 h12
    -- False on the left can always be used.
    apply False.elim h13
  -- Conjunctions on the left can always be decomposed.
  let h14 := h1.left
  let h15 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h14
  case inl h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h15.left
    let h18 := h15.right
    -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
    have h19 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h17, we can now drive its conclusion.
    let h20 := h17 h19
    -- False on the left can always be used.
    apply False.elim h20
  case inr h21 =>
    -- Conjunctions on the left can always be decomposed.
    let h22 := h15.left
    let h23 := h15.right
    -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
    have h24 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h22, we can now drive its conclusion.
    let h25 := h22 h24
    -- False on the left can always be used.
    apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_784919644058240549771401888224 : (((p3 ∨ (p3 → ((((((False → (p1 → p5)) ∧ (p3 → (p2 → p4))) → (p1 → False)) ∨ p4) → (p3 ∧ ((p2 ∨ p2) ∨ True))) ∨ p5))) ∨ False) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h1
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149199191827919526072717873779 : (((p4 → p4) ∧ ((((p3 → False) → p5) ∨ p2) → (((p3 ∨ ((p4 ∧ p2) → p1)) ∨ (p2 ∨ p2)) → False))) ∨ (p2 → ((True → p3) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_609721163538317617716740246660 : (((((p3 ∨ ((((False → p5) → ((True ∧ p3) ∧ ((((p5 → True) ∨ p2) → (p5 ∧ False)) → p5))) ∨ (p2 → p1)) → p1)) ∨ True) ∨ p4) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_137515224942196624040713589832 : ((p5 ∧ (((p3 → (False ∧ True)) ∧ p3) ∨ (p4 ∧ (((p1 ∨ ((p5 ∨ p4) ∧ False)) ∨ p5) ∧ (p4 → (True → p5)))))) ∨ (True → (True ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_633082567809758461580415303248 : ((((((p2 ∨ False) ∧ ((p5 ∨ ((((p3 ∨ p1) ∨ (p2 → p2)) → (p5 ∨ p3)) → p5)) → (p1 ∧ (p4 ∨ p3)))) ∧ (True → p2)) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_859806605129412150541457664825 : (((((((((((p5 → p1) ∧ p3) → p2) ∧ ((p1 ∧ (p2 ∧ (True → (p3 → True)))) ∧ p1)) ∨ p2) ∨ p5) ∧ p1) ∨ (p4 ∨ True)) → False) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((((((p5 → p1) ∧ p3) → p2) ∧ ((p1 ∧ (p2 ∧ (True → (p3 → True)))) ∧ p1)) ∨ p2) ∨ p5) ∧ p1) ∨ (p4 ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204351912560254905303632509777 : (((False ∨ (True ∨ (p4 → p1))) ∧ p3) ∨ ((((((p5 ∧ p5) ∨ p4) ∨ p5) ∨ ((p3 ∧ (p5 ∧ (p1 ∧ p2))) → p1)) ∨ (p3 → p2)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro



