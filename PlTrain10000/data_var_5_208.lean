variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340797007283492042530144081807 : (p2 → (((p1 ∧ ((False ∨ p1) ∨ ((p2 → False) → ((p1 ∨ False) ∨ (p4 ∨ (p5 → (((p3 → p5) ∨ (p5 ∧ p3)) → p2))))))) → p4) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166125907974056605202308380586 : ((True ∧ ((p1 ∨ ((p4 ∧ (True ∧ p4)) → (p2 → (p3 → (p4 ∧ p4))))) → (p4 ∧ p5))) ∨ ((p3 ∧ False) → ((p5 ∧ (p5 ∨ p2)) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38253522045849381629838765957 : (((((p3 ∧ (p2 ∧ p1)) ∨ (p2 ∧ (p2 ∧ ((p3 → p2) ∧ ((False → (p3 ∧ False)) ∧ False))))) ∧ ((True ∧ (True → p4)) ∧ p3)) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809158202512088441101248163949 : (((p5 → (((True ∧ (((p2 ∨ ((False ∧ p2) ∨ ((p3 ∧ ((p3 ∧ p2) ∨ p4)) ∨ (p5 → (p5 → p4))))) → p4) ∧ p1)) ∨ p1) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134561202129393094133481827158 : ((((p3 ∨ (p2 → (((((((True → p5) ∨ False) ∧ (True → False)) → (False ∧ p2)) → p1) → p4) ∨ p5))) → p3) → p5) ∨ ((p2 ∨ p1) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749863872756466310679519422012 : (((True ∧ ((p3 → ((((((False ∧ ((p3 ∨ p4) ∧ False)) → (p5 ∧ p2)) ∨ ((False ∧ p2) → p5)) → (True ∨ p5)) → p4) ∨ p1)) ∨ True)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_337421632217115083342212739941 : (p1 → ((((p4 ∨ (p3 ∨ (p5 ∨ (p1 → ((p4 ∧ p5) ∧ (p4 → p2)))))) ∨ (p3 ∨ (p3 → p5))) ∧ (True ∧ p1)) → (False ∨ (False → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
      -- Conjunctions on the left can always be decomposed.
      let h7 := h4.left
      let h8 := h4.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h4.left
        let h13 := h4.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h14
        -- False on the left can always be used.
        apply False.elim h14
      case inr h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h16 =>
          -- Conjunctions on the left can always be decomposed.
          let h17 := h4.left
          let h18 := h4.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h19
          -- False on the left can always be used.
          apply False.elim h19
        case inr h20 =>
          -- Conjunctions on the left can always be decomposed.
          let h21 := h4.left
          let h22 := h4.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h23
          -- False on the left can always be used.
          apply False.elim h23
  case inr h24 =>
    -- Disjunctions on the left can always be decomposed.
    cases h24
    case inl h25 =>
      -- Conjunctions on the left can always be decomposed.
      let h26 := h4.left
      let h27 := h4.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h28
      -- False on the left can always be used.
      apply False.elim h28
    case inr h29 =>
      -- Conjunctions on the left can always be decomposed.
      let h30 := h4.left
      let h31 := h4.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h32
      -- False on the left can always be used.
      apply False.elim h32



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747209109571236426697244517891 : ((((p5 ∨ p1) → ((((((p5 ∨ p3) ∨ False) → (((p1 → (True → (True → p3))) ∨ (p3 ∧ p4)) ∨ p2)) → False) → p4) ∧ (p2 → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336054815490142306230849276165 : (p1 → ((p4 → (((p5 ∨ (p4 ∧ ((((((p4 ∧ p1) → False) ∨ p1) ∨ ((p1 ∧ p4) → False)) ∧ p4) ∧ (p3 ∨ p3)))) ∧ p2) ∨ True)) ∧ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324305761923568960322421473270 : (p5 ∨ ((p3 ∧ (p2 → (p4 ∧ ((p5 ∧ True) ∨ p1)))) → ((((((p3 ∧ ((False ∧ (True ∧ p4)) → p4)) → p2) → p5) ∧ p1) ∨ p2) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137968881522815020346500401652 : ((p5 ∨ (((p2 ∨ p1) ∧ (False ∧ (p3 → (p3 → (p2 ∧ ((p3 ∧ p2) ∧ p5)))))) ∨ ((False ∨ (p5 → p5)) ∨ p3))) ∨ (False ∧ (True ∨ p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_444457044552810374159676654052 : ((((p5 ∧ (((p4 ∧ p3) ∨ p5) ∧ (p4 ∧ (p3 ∨ (p5 → (((True ∧ ((True ∧ p5) ∧ p5)) ∧ p3) ∧ True)))))) ∨ ((False ∧ False) → False)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219347477082517806627284904622 : ((p2 ∨ (p4 → (p3 ∨ False))) → ((((False ∨ True) → ((p3 ∧ ((p2 ∧ (p1 ∨ True)) ∧ False)) ∨ False)) ∧ (p4 ∨ p4)) → ((p1 ∨ p5) ∨ p5))) := by
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
    cases h1
    case inl h6 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h7 : (False ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h8 := h3 h7
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- Conjunctions on the left can always be decomposed.
        let h14 := h12.left
        let h15 := h12.right
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h16 =>
          -- False on the left can always be used.
          apply False.elim h13
        case inr h17 =>
          -- False on the left can always be used.
          apply False.elim h13
      case inr h18 =>
        -- False on the left can always be used.
        apply False.elim h18
    case inr h19 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h20 : (False ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h21 := h3 h20
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h22 =>
        -- Conjunctions on the left can always be decomposed.
        let h23 := h22.left
        let h24 := h22.right
        -- Conjunctions on the left can always be decomposed.
        let h25 := h24.left
        let h26 := h24.right
        -- Conjunctions on the left can always be decomposed.
        let h27 := h25.left
        let h28 := h25.right
        -- Disjunctions on the left can always be decomposed.
        cases h28
        case inl h29 =>
          -- False on the left can always be used.
          apply False.elim h26
        case inr h30 =>
          -- False on the left can always be used.
          apply False.elim h26
      case inr h31 =>
        -- False on the left can always be used.
        apply False.elim h31
  case inr h32 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h33 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h34 : (False ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h35 := h3 h34
      -- Disjunctions on the left can always be decomposed.
      cases h35
      case inl h36 =>
        -- Conjunctions on the left can always be decomposed.
        let h37 := h36.left
        let h38 := h36.right
        -- Conjunctions on the left can always be decomposed.
        let h39 := h38.left
        let h40 := h38.right
        -- Conjunctions on the left can always be decomposed.
        let h41 := h39.left
        let h42 := h39.right
        -- Disjunctions on the left can always be decomposed.
        cases h42
        case inl h43 =>
          -- False on the left can always be used.
          apply False.elim h40
        case inr h44 =>
          -- False on the left can always be used.
          apply False.elim h40
      case inr h45 =>
        -- False on the left can always be used.
        apply False.elim h45
    case inr h46 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h47 : (False ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h48 := h3 h47
      -- Disjunctions on the left can always be decomposed.
      cases h48
      case inl h49 =>
        -- Conjunctions on the left can always be decomposed.
        let h50 := h49.left
        let h51 := h49.right
        -- Conjunctions on the left can always be decomposed.
        let h52 := h51.left
        let h53 := h51.right
        -- Conjunctions on the left can always be decomposed.
        let h54 := h52.left
        let h55 := h52.right
        -- Disjunctions on the left can always be decomposed.
        cases h55
        case inl h56 =>
          -- False on the left can always be used.
          apply False.elim h53
        case inr h57 =>
          -- False on the left can always be used.
          apply False.elim h53
      case inr h58 =>
        -- False on the left can always be used.
        apply False.elim h58



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_143421773624931421515867689837 : ((p5 → (p4 ∨ (True ∧ ((((p5 ∧ (False ∨ p1)) ∧ ((p5 ∨ p5) ∧ p4)) → ((p1 ∨ False) ∧ (p1 ∨ True))) ∧ p3)))) → ((p4 → p2) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322560513733083284721868363118 : (p5 ∨ ((p2 ∨ ((False ∧ ((p3 ∨ (((((p2 ∧ p4) ∧ (p4 → p3)) → ((p5 ∨ (p5 → p2)) ∧ p5)) ∨ False) ∨ False)) ∨ p4)) ∨ True)) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343381669082908941495013440582 : (p2 → ((False ∧ False) ∨ (((((p5 ∧ True) → p5) → p5) ∨ (p4 → ((((p5 ∧ p2) ∨ p4) ∨ p1) ∨ (p3 ∨ (p2 ∨ p3))))) ∨ (p3 → p4)))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172434425071365982123872580638 : (((False → (False → (True ∧ p2))) ∧ ((True ∧ p5) → ((p3 ∧ p3) ∨ (p1 ∧ p3)))) ∨ ((False ∨ p2) → (((p1 ∨ True) ∨ (p1 ∨ p5)) ∨ p1))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322480549122979792006133546693 : (p5 ∨ (((p4 → p2) ∧ (((p4 ∨ (False → False)) ∨ p5) → (((p4 ∧ p4) ∧ (True ∧ ((p3 → p1) ∧ (p4 ∧ p2)))) ∧ (p5 ∧ p3)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_752232970510928077334044772002 : (((True ∧ (p4 → ((((p5 ∨ ((p2 ∧ p1) → (True ∧ False))) → (p1 ∧ p3)) ∧ ((True ∧ True) → ((True → p5) ∨ p4))) ∨ (p2 ∨ True)))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_593574032286912918491400588991 : (((((p5 ∨ (((p5 → p2) ∨ (((p5 ∧ (p3 → p4)) → p4) ∨ (p2 ∨ ((False ∨ p1) ∨ True)))) ∧ p2)) → ((p3 ∧ False) ∨ p3)) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_927681989769119722723692269289 : (((((True → (p5 → (p5 → ((p5 → True) ∨ p4)))) → False) ∧ (((p1 → (p3 ∧ (p4 → ((p1 ∨ False) → p1)))) ∧ p5) ∨ (p3 ∧ p4))) → p4) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : (True → (p5 → (p5 → ((p5 → True) ∨ p4)))) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- Implications on the right can always be decomposed.
      intro h9
      -- Implications on the right can always be decomposed.
      intro h10
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h11
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h12 := h2 h7
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- One of the premise coincides with the conclusion.
    exact h15
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310873229347933753395086510947 : (p2 ∨ ((p5 ∧ (p2 → True)) → ((((((p1 ∧ ((p1 ∧ (p2 ∨ p5)) → (True ∧ p5))) ∨ p3) ∨ False) ∧ False) ∨ (p5 ∨ p2)) ∨ (True ∧ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_754660246543917600619476429091 : (((False ∧ (p4 ∧ (((p5 ∧ False) ∨ (((p3 ∧ True) ∨ p1) ∨ (p2 ∧ ((p5 ∨ False) ∨ ((True ∧ p2) ∨ True))))) ∨ ((p4 → p2) ∨ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184276525043092994753773503109 : ((((p2 → ((p3 ∧ (True ∧ False)) ∧ p3)) → (False ∧ p4)) → p2) ∨ ((((p1 ∧ p1) ∨ (p1 → p5)) ∧ (p3 ∨ False)) ∨ ((True → p4) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113521746514579671679192587190 : ((((((False → (p4 → p5)) ∨ p3) → (True → (False → False))) → ((p2 ∧ ((True ∨ p3) ∧ p1)) ∧ (p3 ∧ False))) ∨ (p4 ∨ False)) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638295483408418916560934244791 : (((((((p3 ∨ (p5 ∧ p3)) ∨ p1) ∨ False) ∧ ((p2 ∨ (((p4 ∨ (True → True)) ∧ p1) ∨ (p1 ∧ p2))) ∨ (True ∨ (p1 ∨ p4)))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123485641619554227469839586522 : ((((((((False ∧ p5) ∨ (p3 → (p1 → (p1 → p3)))) → True) ∧ p4) ∨ True) → False) ∧ (p2 ∨ (((p4 → p2) ∨ p1) → p5))) → (False ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : (((((False ∧ p5) ∨ (p3 → (p1 → (p1 → p3)))) → True) ∧ p4) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h8 : (((((False ∧ p5) ∨ (p3 → (p1 → (p1 → p3)))) → True) ∧ p4) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h9 := h2 h8
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184994386380388108304663091747 : (((p1 ∧ p5) ∧ ((False ∨ (p2 ∧ p4)) ∨ (p2 ∧ (p3 ∨ p1)))) ∨ ((p2 ∨ (p4 → False)) → (p5 → (((False ∧ p5) ∨ (False ∧ p3)) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181204965615707436783723012765 : ((p2 ∧ (((p3 ∨ (True ∨ p1)) → (True ∨ (p2 ∧ p3))) → (p2 → p3))) → (p3 ∨ (((False ∧ p1) ∨ p1) ∧ ((p3 ∧ False) ∨ (p4 → p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((p3 ∨ (True ∨ p1)) → (True ∨ (p2 ∧ p3))) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
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
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h10 := h3 h4
  -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
  have h11 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h10, we can now drive its conclusion.
  let h12 := h10 h11
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_687280208798829767540677925142 : (((((((p3 → (p3 → p3)) ∨ ((p5 → p2) ∨ True)) ∧ ((p1 ∧ p2) ∧ p4)) ∧ True) ∧ ((p2 ∨ (((p2 → p4) ∧ p4) ∧ p3)) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40970540977675982563293820578 : ((((((p5 ∧ p5) → (p2 ∧ p4)) → ((p2 → p5) ∨ (True ∨ ((p5 ∨ (p1 → True)) ∧ (p5 ∧ (p2 ∧ p4)))))) ∨ (p2 → p5)) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_700475631723198819857661549866 : ((((p2 ∨ (((p4 ∧ ((p3 ∨ p4) ∨ p4)) → p1) ∧ (p2 → p4))) → (p1 → ((p3 → ((p5 ∨ p1) → p4)) ∨ ((True ∧ p4) → p4)))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- One of the premise coincides with the conclusion.
    exact h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809292466646343550579069449312 : (((p5 → (((p4 ∧ p1) ∧ (((False → (False ∧ p1)) → p1) → (((True → ((False ∨ ((p5 ∧ p3) ∨ True)) → False)) ∧ p5) ∨ p5))) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160141004416985695981347831017 : ((((((True → p1) ∧ (True ∨ (p4 ∨ ((p3 ∨ False) ∧ p2)))) ∨ (False → p3)) → False) ∧ (p2 ∨ True)) → (((p5 ∨ False) ∧ p5) ∨ (p3 ∧ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : (((True → p1) ∧ (True ∨ (p4 ∨ ((p3 ∨ False) ∧ p2)))) ∨ (False → p3)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h6
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h5
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h9 : (((True → p1) ∧ (True ∨ (p4 ∨ ((p3 ∨ False) ∧ p2)))) ∨ (False → p3)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- False on the left can always be used.
      apply False.elim h10
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h11 := h2 h9
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219205258062208944636227881787 : ((False ∨ (p5 ∨ (p3 ∧ p1))) → ((p2 → ((((((p1 ∨ p4) → p2) → (p2 ∨ p5)) → (False ∨ p5)) → False) → ((p2 → True) ∧ p5))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h5
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h7
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61369164030718821476094817040 : ((p1 ∧ ((p5 → ((((True ∧ p5) ∨ (p3 ∨ ((False ∧ (p4 → True)) → True))) → ((p5 ∨ ((p4 ∧ p4) ∨ False)) ∨ p2)) → False)) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244423938210274011292432519500 : ((False ∧ p1) ∨ (p5 → ((((((p4 ∨ p5) → (((p1 ∨ (p5 ∧ p2)) ∧ True) → p4)) ∨ p3) ∧ True) ∨ p3) → (((p5 → False) → p2) ∨ p1)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h7
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h8 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h1
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h9 := h7 h8
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h11
      -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
      have h12 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h1
      -- We have shown the premise of h11, we can now drive its conclusion.
      let h13 := h11 h12
      -- False on the left can always be used.
      apply False.elim h13
  case inr h14 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h15
    -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
    have h16 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h15, we can now drive its conclusion.
    let h17 := h15 h16
    -- False on the left can always be used.
    apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40624725620546941102072062128 : ((((((((p4 ∧ ((((((p3 ∨ p2) ∨ False) → p1) ∨ p1) ∧ True) ∧ p2)) ∧ ((False ∧ False) ∨ p3)) → p5) ∧ p1) → p5) → p4) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312089853724714627166106245536 : (p2 ∨ (p5 ∨ (False ∨ (((p4 ∧ ((p4 ∨ (True ∧ p2)) → ((p3 ∧ p4) ∨ p5))) ∨ (((p2 ∧ True) ∧ (p5 ∨ p5)) → p2)) ∨ (p5 ∨ p1))))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678392955200088970803095585374 : (((((True → (p1 → ((p4 ∨ p1) ∨ p2))) → (p4 ∧ (p3 ∨ (((p4 → p3) ∨ False) → (p5 ∧ p5))))) ∨ (((p5 ∧ False) → p5) ∨ False)) ∨ False) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229797261380791845104967093167 : ((p4 → (p3 → p1)) ∨ (((False ∧ True) ∧ (p2 ∧ (p4 ∧ (((True → p1) → (p1 → p3)) ∨ p1)))) ∨ (True ∨ ((True ∨ (p1 ∨ p4)) → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618128078056473214497096745825 : (((((p5 ∧ (p1 ∨ (p2 ∧ p3))) ∧ (p5 → ((p5 ∧ (((p5 → p1) ∨ (p1 → ((p2 ∨ p3) → (p1 ∧ p5)))) → p1)) → p3))) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_215322996347830040979210547832 : ((p1 ∧ (p3 ∧ (p1 ∨ p2))) ∨ ((True → (p3 ∧ ((False ∨ True) ∧ p3))) ∨ (False ∨ (p5 ∨ (((p5 ∧ p3) → (p5 ∧ (False → p5))) ∨ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328713593446882814469166377771 : (True → ((p4 ∧ (((((p3 → (True ∧ False)) → p3) ∨ p5) → False) ∧ p2)) ∨ (p4 → (((p4 ∨ ((p4 ∧ p4) ∨ p5)) ∧ p4) ∧ (p4 ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134356195618497655593470921262 : (((False ∨ (((((p1 → p1) ∧ ((p2 ∨ p1) → p3)) ∧ (p1 → (p1 ∧ False))) ∨ ((p4 ∧ p3) → p5)) → p3)) ∨ p3) ∨ ((p1 ∧ p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208879778965536124881117533514 : ((p4 ∧ (p2 ∧ (p3 ∨ (p5 ∧ p5)))) → (p3 ∨ ((p1 ∧ (p4 ∧ p3)) ∨ (((False → ((p1 → p1) → (False ∨ p1))) → p3) ∨ (p5 → p5))))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_98817125585449733714543370403 : ((True → ((((p4 ∨ p4) → False) ∨ (True → (p1 → ((((p3 ∨ (p2 ∨ p1)) ∧ (p4 ∨ (p5 ∨ False))) ∨ (True → p4)) ∧ p4)))) ∧ False)) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148157117386315421594690466652 : (((p1 → (p3 → ((((((True → ((p1 → p4) ∧ p3)) ∨ p4) → p3) ∧ True) → p2) ∨ False))) → (p4 → p3)) ∨ ((p5 → (False → p4)) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148025660859396752321405852514 : ((((((p1 ∨ p5) → p3) ∨ p5) ∧ ((p2 ∨ (p5 → (((p2 ∧ p1) → p5) ∧ p5))) → p2)) ∨ (False ∨ p4)) ∨ (((True → p2) ∧ p5) → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_811250244746685284526958901103 : (((p5 → (p5 ∧ ((p2 ∧ False) ∨ (((True → (p1 ∧ p1)) ∧ (((True ∧ (p2 → p2)) → (False ∨ False)) ∧ p1)) ∨ (p4 → (p2 ∧ p4)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59928861364601392669237760727 : (((p5 ∧ p5) → (p5 → ((p3 ∨ ((p5 ∧ (p2 ∧ ((p1 ∧ p5) ∨ False))) ∨ (((p3 ∧ p1) ∧ p4) ∨ (False ∧ (True → p2))))) ∨ True))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196805242537597795419733420476 : ((((True ∨ p4) → ((p2 ∨ p1) ∧ p1)) ∧ p5) ∨ (((p2 → p3) ∨ p1) ∨ (p2 → (False → ((p2 ∨ p5) → (((p4 → p4) → p5) → p1)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_756539831861771812550964943871 : (((p1 ∧ ((((((p2 ∧ (False ∧ (p3 ∧ p5))) ∨ p3) ∨ p4) → True) ∨ (((False → p5) ∨ False) ∧ p2)) → (p5 ∧ (False → (p1 → p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138274520262689813493990866468 : ((p3 → (((((p1 ∧ (False ∧ p4)) ∨ p2) ∨ p3) → ((p5 ∨ (False ∨ p4)) ∨ (p4 ∨ ((p5 ∧ p3) ∨ p3)))) ∧ p5)) ∨ ((p5 ∧ False) → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64543379377856551749544345928 : ((p1 ∨ ((p5 ∧ ((p5 ∧ p1) ∧ (False ∨ p3))) ∨ (((p2 → (((p5 ∧ (p3 → p4)) ∧ (p5 ∨ (p4 ∨ p2))) ∧ p3)) ∧ p1) → True))) ∨ p3) := by
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
theorem thm_5_vars_50962257308913950210023544060 : ((((p2 ∨ (p2 → ((True → True) ∧ p4))) → (((True ∧ p5) → (False ∧ p3)) ∧ (False ∧ False))) ∧ (((p2 → p4) ∧ (p3 ∨ p4)) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138421746051201895487366134776 : ((p5 → ((p1 → ((p4 ∧ False) ∧ ((((p1 ∨ p4) ∧ p2) ∧ (p5 → True)) ∧ ((p5 → (p2 ∨ True)) ∧ True)))) → False)) ∨ (p1 ∨ (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_759041783380633256561160721737 : (((p2 ∧ ((p3 ∨ (((False → ((p5 ∧ p1) ∨ ((False → p3) ∨ (p3 ∨ ((False ∧ (p5 ∧ True)) ∧ p1))))) ∨ p5) → (p2 ∧ p1))) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249868395362422430238040288342 : ((True → False) ∨ ((p2 → (p1 ∧ p5)) → ((p1 → p2) ∨ ((((p5 ∧ p5) → p5) → (True ∧ (p1 → (p3 ∨ ((True → p1) ∨ p5))))) ∨ p1)))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65340743403323573381304679970 : ((p3 ∨ ((((((True ∨ p4) ∨ p4) ∨ (p4 → (p3 → True))) ∧ False) ∧ ((p3 ∨ False) → p2)) ∧ ((p3 → p2) → (True ∧ (False ∧ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354145208438009328735792159679 : (p5 → (((((p1 ∧ ((True ∨ p3) ∧ p5)) ∧ ((p2 → p2) → ((((p2 → p5) ∧ p1) ∧ (p2 ∨ p3)) ∧ p2))) ∨ (True ∧ True)) ∧ p5) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136739262843677240602666219892 : (((False ∨ False) ∧ (((p3 ∧ (p5 ∨ ((p4 ∨ (p3 → True)) ∧ (p1 ∨ p2)))) ∧ (p2 ∧ ((p5 → False) → p5))) ∨ p1)) ∨ ((p3 → p3) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729341312746988741954787397555 : (((((p1 ∧ p5) ∨ p5) → (((((p4 → p3) ∧ False) ∨ (p4 ∧ (p2 ∧ True))) ∧ (p3 ∧ ((((p3 → p3) ∨ False) ∧ p1) → p5))) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303962974847143604413977757236 : (p1 ∨ (((p1 ∧ (p3 → p3)) ∧ (((True ∨ p4) → p5) → (((p5 → p2) ∨ ((p3 ∨ False) ∧ p2)) ∧ ((True ∨ (p1 ∨ p1)) → p2)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301255144925343496517779812492 : (False ∨ (((p2 ∧ p1) ∧ ((True → False) ∨ p2)) ∨ (p5 ∨ (p4 ∨ (True ∨ (((p4 ∨ p3) → (p1 ∨ p1)) ∧ ((p3 → (p1 ∨ p3)) → p3))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_246588778312909735063917501394 : ((p5 ∧ p2) ∨ ((True ∨ (True ∧ p4)) → ((p1 ∧ ((((p5 → p4) ∧ p3) ∨ p4) → (p2 ∨ (False ∨ p3)))) ∨ ((False ∧ p2) → (False ∨ False))))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57350096602190824257723410541 : (((p3 ∧ (True ∧ p1)) ∨ ((((p3 ∨ ((p1 ∧ p1) ∨ p5)) → False) ∨ (p1 → (p2 ∧ (p3 → (True → (p4 ∨ (p4 → True))))))) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712123510514139409067439467340 : (((((True → (p4 ∨ (p2 → p4))) ∨ p4) ∨ (False ∨ ((p1 → ((p5 ∧ False) ∨ (p4 ∨ ((True ∧ (p1 ∨ p1)) ∧ p4)))) ∧ (True ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200564496889408163651875520847 : (((p4 → p5) → (((True ∧ p3) → True) ∨ p1)) → (((True → p1) → (p3 ∧ (((((True ∧ p4) ∨ True) ∧ p3) → p1) ∧ p1))) → (p5 → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191236527745963404861114913717 : (((p4 → (True ∧ p1)) → ((p2 → p4) ∧ (True ∨ False))) ∨ (False ∨ (True ∨ ((p1 → p1) → ((True → ((p2 ∨ (False ∨ p3)) ∨ True)) → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341742729937377405505918014381 : (p2 → ((True ∧ (((p4 → False) ∧ ((p2 ∧ p5) ∧ p3)) → (((p4 ∧ (p2 ∧ True)) ∧ (p2 → (False ∧ (p1 ∨ p1)))) ∨ p4))) ∨ (p3 ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148928179709481316980663041328 : ((((p3 ∧ p2) ∨ (p3 → p1)) → ((True → (False ∧ (((True → ((p4 ∧ False) → p5)) → p4) → p2))) ∨ False)) ∨ (p5 → (p1 → (p5 ∧ p1)))) := by
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
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259005459150896458339238963292 : ((True → p4) → (((((p2 → False) → False) ∧ (((p3 → True) → (p3 ∧ (p5 → p1))) → ((p5 ∨ False) → ((False ∧ p3) ∨ True)))) ∧ False) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343424313809542872376373496278 : (p2 → ((False ∨ p4) ∨ (((((p1 ∧ (p4 ∧ (p2 ∧ p1))) → ((p5 ∧ p3) ∧ p1)) → p3) ∨ (p5 → True)) ∧ (True → ((p1 ∧ p4) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720990476083158441883324515179 : (((((p1 → p2) ∧ (p4 ∨ p4)) → (((((p2 ∨ p3) ∨ ((True ∨ ((p1 ∧ p2) ∨ p4)) → p2)) ∨ True) ∧ p1) ∨ (p3 → (p3 → True)))) ∨ False) ∧ True) := by
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
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_7701950774802168544286574360 : ((((((p4 ∨ (p5 ∧ p4)) ∨ (p1 ∨ ((((p2 → p3) → ((True → True) → ((False ∨ p1) ∧ False))) ∧ p1) ∧ False))) ∨ True) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_710941123265893259542675524939 : (((((p5 ∨ p3) ∨ ((True ∧ p5) ∨ p3)) ∧ (((p1 → (p5 → False)) ∧ p4) ∨ (((((False ∧ False) ∧ (p5 ∨ False)) ∨ False) ∨ True) → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_646284077237390315416398822865 : ((((False → (((p3 → (p3 ∨ True)) ∧ False) → ((p5 ∨ (p5 ∧ (p1 ∧ (p2 → p1)))) ∨ (False ∨ ((p3 ∨ False) ∨ (p2 ∧ p5)))))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157795173524271449720405615983 : (((p1 ∧ (p1 ∨ (p4 ∧ (((False ∧ (p3 ∧ False)) ∧ p5) ∧ p3)))) ∨ ((False ∧ p5) → (p1 ∧ p2))) ∨ (p2 → (((p3 ∧ False) ∧ p1) ∧ p1))) := by
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
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_588355123085213422545412368220 : ((((((p1 ∧ (p1 ∧ (True ∧ p1))) → (((p3 → ((False ∨ (p4 ∨ (False → (p3 ∧ p1)))) ∧ (False ∨ p5))) → p3) ∧ True)) ∨ True) ∧ True) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_52307889910796258039268650739 : ((((p5 ∨ ((((p4 ∨ False) ∧ ((p3 ∧ p1) ∧ p3)) ∨ p1) ∧ False)) ∧ False) ∧ ((p2 → p1) ∨ (p2 → ((True ∧ p3) ∨ (p2 → p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165126826064015265590223771384 : ((((True ∧ (((p2 ∧ True) → ((p5 ∧ p3) ∧ (False ∧ True))) ∧ False)) ∧ p5) ∧ (p1 ∧ p1)) ∨ (p4 ∨ (p3 ∨ ((p4 → p3) → (p4 → p3))))) := by
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64495716191705040003075926566 : ((p1 ∨ ((False ∨ ((p2 ∨ (((p1 → p2) ∨ (((True ∨ True) ∨ False) → p5)) ∨ p2)) → p1)) ∨ (True ∧ (((p1 ∨ True) ∨ p4) ∨ p3)))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618345411766087068386606846514 : (((((p5 ∧ (p1 ∧ (p1 ∧ p4))) ∨ ((True ∧ (((False → p3) ∧ (((True ∨ (p5 → p4)) ∧ p4) ∨ False)) → True)) → (p3 ∨ True))) ∨ p3) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233546353081425069334522799042 : ((p1 ∨ (p5 ∨ True)) → (((p5 → (p3 ∧ p1)) ∧ (p4 → True)) ∨ ((False ∨ (p5 → (((p3 ∨ (False ∨ p5)) ∨ p1) ∨ (True → True)))) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41508217199389736625944292402 : ((((p1 → ((p5 ∧ p2) → ((False ∨ (p4 ∧ (True ∨ False))) → p2))) → (p1 ∨ (p5 ∨ ((((p4 ∨ p3) ∨ p3) → p5) → p2)))) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_750454196523707334466725181334 : (((True ∧ (((p5 ∧ p5) ∨ (((p3 ∨ (p4 ∨ p1)) ∨ p2) ∨ ((p2 ∧ (p2 ∨ p5)) → (True → (True ∧ p2))))) ∨ (True ∧ (p1 ∧ p4)))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  cases h4
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180969917499925266411540860447 : (((p2 → p4) ∧ (((p2 ∧ (((p3 ∧ False) ∧ p2) ∧ p4)) → True) ∧ p1)) → (p1 ∧ (((p3 ∧ p4) → (False ∧ p4)) → ((p4 ∨ p1) ∧ p1)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h10
  -- Conjunctions on the left can always be decomposed.
  let h11 := h1.left
  let h12 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h13 := h12.left
  let h14 := h12.right
  -- One of the premise coincides with the conclusion.
  exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61242087930741146830070783708 : ((False ∧ (p4 ∧ ((p4 ∨ (((p5 ∧ p3) ∨ (((p1 ∨ p2) ∧ (p3 → p5)) ∨ ((p5 → p3) → (True ∨ p4)))) → p2)) ∨ (p5 ∨ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64107535307526236127505460784 : ((False ∨ (((p4 ∨ p5) ∨ (p3 ∨ ((False ∨ True) ∨ False))) ∨ (True → ((((False ∨ True) → p4) → p4) ∨ ((True ∨ p4) ∨ (p2 ∨ False)))))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_87283307857860827873867745365 : (((((p2 → p4) ∧ (False → True)) → False) ∧ ((p2 → (p4 ∨ ((p3 ∧ (p2 → ((True ∨ (p3 ∧ True)) ∧ p1))) ∧ True))) ∧ (p3 → p4))) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : ((p2 → p4) ∧ (False → True)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h7
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h8 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h9 := h4 h8
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Conjunctions on the left can always be decomposed.
      let h14 := h12.left
      let h15 := h12.right
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h16 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h14
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h17 := h5 h16
      -- One of the premise coincides with the conclusion.
      exact h17
    -- Implications on the right can always be decomposed.
    intro h18
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h19 := h2 h6
  -- False on the left can always be used.
  apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58811125973371706581790843042 : (((p5 → p3) ∧ (((((True ∧ (((True → True) → True) → ((p2 ∨ p4) ∨ p1))) ∧ p2) ∨ ((p1 ∧ p3) ∨ p2)) ∧ (p3 ∨ True)) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178881490202405497380981332904 : (((p3 ∧ False) ∧ ((((p2 → (p3 → p5)) ∨ p4) → (False ∧ False)) ∨ p3)) ∨ (((True → ((True ∧ True) ∧ (p3 → p1))) ∧ (False ∧ p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64360978826601394020764583994 : ((p1 ∨ ((((((False → True) → p3) → p4) → (p1 → (p2 ∧ (p5 ∧ ((p5 → False) → (p1 → p2)))))) → ((p3 ∧ p3) → False)) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174074188275000954424532822508 : ((((((p2 → (False → p3)) ∧ p1) → ((p3 → p4) → p5)) ∨ p4) ∧ (False → True)) → ((True → True) → ((((p4 → p3) → p4) → False) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113143971980996479018861380428 : (((p3 → (((((p5 ∧ (p5 ∧ p3)) ∨ ((((p1 → p5) ∨ False) → False) ∨ (p1 ∧ p2))) ∧ p5) → (p4 ∨ False)) ∨ True)) → p1) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_653914850243236590589664511407 : ((((((p5 ∨ True) ∧ ((p1 ∧ True) ∨ (p4 ∨ ((p4 ∨ ((p4 ∧ ((p1 → p5) → (p1 → p5))) ∧ p3)) → p2)))) ∧ p5) ∨ (p1 ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117091366945299596100016216094 : (((p1 → p1) → ((((p1 ∧ True) → ((p5 ∧ False) ∧ (((True ∧ (p3 → p4)) ∧ ((p2 → False) → p5)) ∨ p4))) ∧ False) ∧ p4)) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185179640752730822307924717992 : (((p4 → False) → ((((p2 ∧ (False → p3)) ∧ p1) ∨ p3) ∧ False)) ∨ ((p4 ∧ p1) → ((p5 ∧ (p5 → (p1 → ((p5 → False) ∨ p1)))) → p4))) := by
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
  let h5 := h1.left
  let h6 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112341180556451490025991647458 : (((p5 → ((((True → (False → ((True ∧ p4) ∨ False))) → ((p3 ∨ p3) → ((p4 ∧ False) ∧ p2))) ∨ p5) ∧ (p2 ∧ p2))) ∨ True) ∨ (p2 → True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



