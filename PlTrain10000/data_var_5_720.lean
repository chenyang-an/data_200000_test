variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53717678799096034961546860879 : (((p4 ∨ (False ∨ ((True ∧ (False → (p3 ∧ p1))) → True))) ∧ (((p4 ∧ (False ∨ True)) → (p5 → p2)) → (((True ∨ False) → p3) → p3))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (True ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245726500262282740607137942893 : ((p3 ∧ p2) ∨ (((p3 ∨ ((p2 ∧ (p5 → ((False → (p5 ∨ (p3 ∧ False))) ∨ p3))) ∧ p3)) ∨ p2) ∨ (p2 ∨ ((p5 ∨ (p4 → False)) ∨ True)))) := by
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
theorem thm_5_vars_49278212743709779848572618072 : (((p3 ∧ (p2 ∨ (((p5 ∧ p1) ∨ ((p3 → p2) → p3)) → ((((True ∧ p4) → (p2 → p5)) → p1) → False)))) ∨ (False ∨ (p4 ∨ True))) ∨ False) := by
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
theorem thm_5_vars_165922500851904914210549899027 : (((p1 ∧ p5) ∧ (((True ∨ p4) → (p5 ∨ p5)) ∧ (p5 → ((p2 ∨ p5) ∧ (p4 → True))))) ∨ (p4 → (((p3 → p4) ∨ (p1 ∨ p4)) ∨ p3))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200166495478166511282124218288 : ((((p2 ∧ False) → p5) ∨ ((p1 ∨ p3) ∨ p4)) → ((p1 ∨ ((False → (p4 ∧ ((p1 ∧ True) ∨ True))) → p2)) ∨ (p2 ∨ (True ∨ (p3 ∨ p2))))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320370240627576651905636644520 : (p4 ∨ ((p4 → p3) ∨ ((((p5 → (p2 ∨ True)) ∨ p4) → False) ∨ ((p2 ∨ (((p2 → p3) ∨ True) → (True ∨ (p5 ∧ p2)))) → (p2 ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217129328723950932320938705519 : ((((p5 ∨ p3) ∨ True) ∨ p5) → (p3 → (((p4 → p1) ∧ (p2 → (((p1 ∧ (p5 → (p3 → False))) ∨ (p5 → p4)) ∨ False))) ∨ (p4 ∨ True)))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h6 =>
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
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62926342573433576704798295580 : ((p4 ∧ (p1 ∧ ((p2 ∧ (p5 ∧ (((((p1 ∧ (p5 ∨ False)) → p1) ∨ p5) ∨ False) ∨ p2))) ∨ ((p5 ∨ ((p4 → p3) → p3)) → p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341672506429522484737907336370 : (p2 → ((((p5 → ((False ∨ (((p2 ∨ (False → False)) ∨ (p2 ∧ p4)) ∨ p1)) ∧ True)) ∧ (p1 ∧ (False ∧ (p3 → True)))) ∨ p1) ∨ (p3 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_918838316427611184866316038788 : ((((((p2 ∧ (((p2 → (False ∨ (p4 ∨ False))) ∨ False) ∨ p1)) ∨ p5) → p1) ∧ (((((p5 → p5) → True) ∨ (p3 → p3)) → True) → p5)) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((((p5 → p5) → True) ∨ (p3 → p3)) → True) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h7 : ((p2 ∧ (((p2 → (False ∨ (p4 ∨ False))) ∨ False) ∨ p1)) ∨ p5) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h7
  -- One of the premise coincides with the conclusion.
  exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301283038866682559291647768631 : (False ∨ ((((p5 → (p5 ∨ p3)) ∧ True) → p4) → (((p2 ∧ (p1 ∧ (p5 ∨ True))) ∨ p5) ∨ (p5 ∨ ((p1 → (p4 ∨ p5)) ∨ (True ∨ p2)))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172268971149733848556934411329 : (((((p5 ∨ (p1 ∨ True)) ∧ p5) ∧ (p5 ∧ p1)) ∨ (((p3 ∧ False) ∨ p2) → False)) ∨ (((p4 ∧ (True ∨ (p5 ∧ p2))) → p1) ∨ (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118482355919868116678570158770 : ((p3 ∨ (((True ∧ (p3 ∧ ((((((True → ((p4 → p4) ∨ p1)) → p2) ∧ p5) → False) → p3) → p1))) → p1) → (p2 ∨ True))) ∨ (False ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112640224274336502585265235630 : ((((False ∧ (p3 ∨ (((((True ∨ p3) → p4) ∧ ((p4 → True) → True)) ∨ ((p5 ∨ p4) ∨ p5)) → p4))) → (p2 ∨ p2)) → p2) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206013950660996966126191421789 : ((p2 ∧ ((p5 → (True → p1)) ∧ p3)) ∨ (((p1 → p5) ∨ (p1 ∨ (p1 → (True → p3)))) ∨ (((p1 → p2) → (p4 → (p1 ∨ True))) ∨ p3))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233862019158868730731599862356 : ((p4 ∨ (p5 ∧ False)) → (((p1 → True) ∨ ((p1 ∨ (p1 ∧ (p2 → True))) ∨ p1)) → (p3 → ((((p2 ∧ p3) ∨ True) → p5) → (True → p5))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h7 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h8 : ((p2 ∧ p3) ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h9 := h4 h8
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h16 =>
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h17 : ((p2 ∧ p3) ∨ True) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h18 := h4 h17
          -- One of the premise coincides with the conclusion.
          exact h18
        case inr h19 =>
          -- Conjunctions on the left can always be decomposed.
          let h20 := h19.left
          let h21 := h19.right
          -- False on the left can always be used.
          apply False.elim h21
      case inr h22 =>
        -- Conjunctions on the left can always be decomposed.
        let h23 := h22.left
        let h24 := h22.right
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h25 =>
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h26 : ((p2 ∧ p3) ∨ True) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h27 := h4 h26
          -- One of the premise coincides with the conclusion.
          exact h27
        case inr h28 =>
          -- Conjunctions on the left can always be decomposed.
          let h29 := h28.left
          let h30 := h28.right
          -- False on the left can always be used.
          apply False.elim h30
    case inr h31 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h32 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h33 : ((p2 ∧ p3) ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h34 := h4 h33
        -- One of the premise coincides with the conclusion.
        exact h34
      case inr h35 =>
        -- Conjunctions on the left can always be decomposed.
        let h36 := h35.left
        let h37 := h35.right
        -- False on the left can always be used.
        apply False.elim h37



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350047930071169789362146360642 : (p4 → (((p3 ∨ (p3 ∨ ((p5 ∨ p5) ∧ (True ∨ (((p1 ∨ p4) ∧ (True → p3)) ∨ (p2 ∨ ((p5 ∨ (p5 ∨ p1)) → p5))))))) → p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_472270927780544026920665729360 : (((((p1 ∨ p4) → ((p5 ∨ ((False ∨ p1) ∧ p1)) ∨ (p5 ∨ False))) ∨ ((False ∧ False) → (((p5 ∧ p1) ∨ p1) → (p5 ∧ (p3 ∧ True))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h1.left
    let h7 := h1.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h1.left
    let h10 := h1.right
    -- False on the left can always be used.
    apply False.elim h9
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h1.left
    let h15 := h1.right
    -- False on the left can always be used.
    apply False.elim h14
  case inr h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h1.left
    let h18 := h1.right
    -- False on the left can always be used.
    apply False.elim h17
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_666836009023090382482822141165 : (((((p2 ∨ (((p2 ∧ True) → p1) ∨ (p1 → p1))) → (((p3 → (p3 ∧ False)) ∧ ((p5 ∨ p4) → True)) ∧ p2)) ∧ (True → (p4 ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62154096919493091969420054846 : ((p2 ∧ (p1 → ((((p4 → p2) ∧ ((False → (p4 → (False ∨ False))) ∧ False)) ∨ (((True → p3) ∨ (p4 ∨ p1)) ∧ p3)) ∨ (True ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141298328041375134575593306769 : (((p3 ∧ ((True → p5) ∨ p3)) ∧ ((True → p4) ∧ (p5 ∧ (((p2 → True) ∧ False) → ((True ∧ (p3 ∨ False)) ∨ p4))))) → ((p2 ∧ p4) → p4)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h6.left
    let h11 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h6.left
    let h16 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306436780355724857127152262819 : (p1 ∨ ((False ∨ False) ∨ ((p2 → ((p3 ∨ (((True → False) ∨ True) ∨ (p3 → p2))) ∨ False)) ∨ (p4 ∨ ((((p2 ∨ p1) ∨ p3) ∨ p3) → True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_627052648948054564931158427244 : ((((((((False ∧ True) → p3) ∧ (p1 ∨ (((p5 → (True → ((p4 ∧ p4) ∨ (p5 → p1)))) ∧ (p1 ∨ p4)) ∨ p5))) ∧ p3) ∧ p2) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_131640348227995038180816445648 : (((p5 ∨ (p5 ∧ True)) ∨ (((p5 ∧ (p1 → False)) ∨ True) → ((p4 ∧ p3) → (((p2 → p5) ∧ (True ∧ p1)) ∨ p3)))) ∧ (True ∨ (p1 ∧ p3))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213472091219539905060992635885 : (((False → (True → p3)) ∧ p2) ∨ (((p4 → False) ∨ p4) ∨ (p4 ∨ ((p4 ∧ (p2 ∨ True)) ∨ (False ∨ ((p2 ∨ True) → ((p1 ∨ True) ∨ p2))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259954801284730974375456935464 : ((p1 → p5) → (True ∧ (((False → (p4 → p1)) → False) → (False ∨ (False ∨ (((((p3 ∧ ((p3 ∧ p3) → True)) ∨ p2) ∨ True) → p5) → p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (False → (p4 → p1)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h3
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138310696800720595107023369944 : ((p3 → ((True ∧ (True ∧ p3)) ∧ (((((False → (False ∧ (True ∨ True))) ∨ p4) → (p4 ∨ (p4 ∨ p1))) ∨ True) ∨ p3))) ∨ (p4 → (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_182602371735279545758313447150 : (((((p3 ∧ (p5 → False)) → p3) ∨ p4) ∨ (p3 ∧ (p4 ∨ p2))) ∧ ((((p4 → (p1 → p3)) ∧ (p2 ∨ (False ∨ p4))) ∨ (p4 ∨ p3)) ∨ True)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263105464257552685033188538242 : (True ∧ ((((p1 ∨ (((p4 ∨ (p2 → p5)) → ((False ∨ (p4 ∨ True)) → (p2 ∧ p2))) ∨ p3)) → (p4 → p3)) → (False ∨ p4)) ∨ (False → p4))) := by
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
theorem thm_5_vars_715125481366922102835120384230 : ((((p4 ∨ (p3 → (p3 ∧ (p2 ∧ p4)))) → (((p3 ∨ p5) ∨ (p3 ∧ False)) → (((False ∨ p5) ∨ (p4 ∧ p4)) ∨ (p2 ∧ (True → p2))))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h5 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h5
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h6 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h7 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h4
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h8 := h6 h7
        -- We need to get the right conjuct of h8 based on <expert-advice>.
        let h9 := h8.right
        -- We need to get the right conjuct of h9 based on <expert-advice>.
        let h10 := h9.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h10
        -- One of the premise coincides with the conclusion.
        exact h10
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h12 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h13 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h11
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- False on the left can always be used.
    apply False.elim h16
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217373074138091810354250926567 : (((p4 ∨ (p5 ∨ p3)) ∨ True) → ((((p3 ∧ p2) → (p1 → p4)) ∧ (((p2 ∨ False) → p3) ∨ (p1 → (((p1 ∧ p5) ∧ p1) ∨ True)))) ∨ True)) := by
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
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114049373901031455814707523219 : (((((p4 ∧ ((((p5 ∨ ((False ∧ p2) ∨ True)) ∧ p3) → p5) ∧ p3)) ∨ p5) ∧ (False → (p3 ∧ p4))) ∨ ((True ∨ p5) ∧ p1)) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695564998376927783710575793159 : (((((((True ∨ (p4 → False)) ∨ (p2 → p1)) ∧ False) → ((p4 ∨ p3) → p1)) → (p1 ∨ (False ∨ ((True ∧ p3) ∨ ((p1 ∧ p2) → False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194719360789699015704744951063 : ((((p4 → p5) → ((p3 → False) ∧ False)) ∨ True) ∧ ((p3 ∧ ((p1 ∨ (p4 ∧ p4)) ∨ (p4 ∧ ((p3 → p4) ∧ (p3 ∧ True))))) ∨ (p2 → p2))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355839897747109472720808818312 : (p5 → (((p3 ∨ (((p3 ∨ p5) ∧ (True → (p5 ∨ (((True ∨ (True ∨ p1)) ∧ False) → (p3 ∧ p1))))) ∧ p3)) ∨ p3) ∨ ((p3 ∧ p2) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_808147111747800295431030023541 : (((p4 → (p2 ∧ ((False ∨ ((p2 ∨ (True ∨ True)) ∨ (((p1 ∨ (True → False)) ∧ p5) ∨ (True ∧ p4)))) → ((p2 → (p2 ∧ p3)) ∧ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48414780850445547573051948078 : (((p2 → ((True ∨ (((p5 ∧ False) ∨ p5) ∧ p5)) ∧ (((False ∨ ((p4 → True) → (p3 ∨ p3))) ∧ (p5 ∨ True)) ∧ p2))) → (False ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54267540229745452645392985124 : (((((p1 → True) ∧ p5) ∧ (p5 ∨ (p2 ∨ p1))) ∧ (True → (((((p1 ∧ (p3 → ((p3 ∧ p5) → p2))) → p4) ∨ True) → True) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134504426216044335021652639774 : (((((((p4 → p4) → p5) → p4) → (((p1 ∨ ((p5 ∧ p4) → True)) ∧ p4) ∧ (False ∨ (True ∧ p1)))) ∨ p3) → p3) ∨ (True ∨ (True ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204571346143665505202018387133 : ((((p3 ∨ p2) ∧ (False ∨ True)) ∨ p1) ∨ (((p4 ∨ True) ∨ ((((False → p1) ∧ (p3 ∧ p3)) ∨ p5) ∨ p3)) ∧ (p3 → ((False ∨ p5) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_717309119476043668324145499685 : ((((p4 ∨ (p5 ∨ (p2 → p3))) ∧ ((((False → p1) ∨ p1) → (False ∧ p2)) ∨ (((p5 → ((p5 ∧ p5) ∧ p1)) ∨ (p5 → p1)) ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349053265988546081676530409481 : (p3 → (p5 ∨ ((((p3 ∧ p5) ∧ ((False ∨ (p3 → (True ∧ False))) ∨ p4)) ∨ False) ∨ (((False ∧ ((False ∧ p4) → p2)) ∨ p2) → (p4 ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157792665855935473600093117359 : ((((p5 → p1) ∨ (False ∧ (((p4 ∧ False) → (p5 → p5)) ∧ p1))) ∨ (p1 → ((p1 ∧ p2) ∧ False))) ∨ ((False → True) ∧ ((False ∨ True) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184243355830792735653726412779 : ((((((p3 → False) ∧ p5) ∨ (p1 ∨ (p1 → p3))) → p5) → p3) ∨ (False ∨ (((p4 ∨ ((p1 → p1) ∧ (p2 ∧ p2))) → (p2 → p5)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56678871763701674870501102026 : ((((p3 → p1) ∧ p1) ∧ (((p1 → ((p5 ∧ (p4 ∨ p2)) ∧ p4)) ∨ (p2 ∧ p4)) ∨ ((p3 ∨ (p2 ∨ False)) → (True → (p3 ∧ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_696034766216994118041308424845 : ((((p2 ∧ ((p5 ∧ True) ∨ ((p1 → True) ∨ ((p5 → p1) ∨ (p5 ∨ False))))) → (False ∨ ((p3 ∧ p1) ∨ (p1 → (True → (p4 → p5)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774437843003014597887853256744 : (((False ∨ (((((p4 ∨ (p5 ∧ (p4 → (p1 ∧ p2)))) → (p4 → False)) ∨ (False ∨ p5)) ∧ p3) ∨ (False ∧ ((p1 ∨ p4) ∨ (p4 ∨ p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53068751004533053798143694916 : (((p1 ∧ ((p3 ∨ (p5 ∨ p2)) ∧ (False ∨ (p2 ∧ (p5 → p4))))) ∧ (p5 → ((((p2 ∧ p5) → False) ∨ True) → (p2 → (p5 ∨ p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315390885151178407149808702319 : (p3 ∨ (((False ∨ p3) ∧ p1) ∨ (((False ∧ (((False ∧ p2) ∨ (p3 ∧ p2)) ∨ p3)) → p2) → ((((p5 ∧ (p2 → p2)) ∧ p1) ∧ p5) ∨ True)))) := by
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
theorem thm_5_vars_190008533239914558926459740569 : (((((p3 → (p4 ∨ (True → p4))) ∧ p1) ∧ p1) ∧ p2) ∨ ((((p2 ∨ (True ∨ (False ∨ (p2 ∨ (p3 → p1))))) ∨ p5) → (p5 → True)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337061284464428995184469878546 : (p1 → ((((((False ∧ ((p1 → False) ∧ True)) → p4) ∨ (p2 → p2)) → (True → (p2 → (True ∨ ((True ∨ p3) ∨ p2))))) → p2) ∨ (p1 ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48550595179843419687096532481 : ((((((((p3 ∨ False) ∧ p1) ∨ (p3 ∨ p3)) ∧ ((p2 ∧ (p2 ∧ ((p1 ∧ p4) → p1))) ∧ p2)) → p5) → False) ∧ ((p5 ∨ p4) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655980424872153370755228258362 : ((((((((False ∨ (p2 → p2)) → p3) → ((p5 ∨ ((p3 ∨ p5) → p2)) → p3)) → p1) ∨ ((p4 ∧ (p4 ∧ p2)) ∧ p3)) ∨ (True ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_760082439257423614941035165725 : (((p2 ∧ (((p2 ∧ p3) ∧ p4) ∨ ((p4 → (((True ∨ ((True ∧ p5) → False)) → False) → p2)) ∨ (p2 → ((True ∧ p4) ∨ (p5 → False)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204710726863160216778824264925 : (((p5 ∨ (p4 ∨ (p1 ∧ p1))) ∨ p3) ∨ ((p2 ∧ p3) → ((p1 ∨ (p2 ∧ (((p2 ∧ (p1 ∧ p4)) → p3) → p1))) ∨ ((p5 ∨ p3) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41629643839235509049514049961 : (((((True ∨ p5) ∧ (((p1 → p5) → p2) → p5)) → (((p1 → False) ∧ True) → ((p1 → (False ∨ p3)) ∨ (p5 → (p2 ∨ True))))) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_99036863041027597737473320330 : ((True → (((p1 ∧ p3) ∨ (p3 ∧ p4)) ∧ (((p3 ∨ (p1 → False)) → (p1 ∧ ((p1 → (p1 ∧ p5)) ∨ p5))) ∧ ((p5 ∧ False) ∧ p5)))) → p4) := by
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
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_764410094033326512104125559760 : (((p4 ∧ ((p1 ∧ (((p4 → p2) ∨ True) ∧ ((p5 ∨ p3) ∨ ((False ∨ p1) → (p2 ∧ ((p2 → False) → (p4 ∨ (p5 → p2)))))))) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234390322783488331717680928181 : ((p1 → (p1 → False)) → ((p2 ∨ (((((p5 → p3) → (((p4 ∨ p5) ∧ False) ∧ p5)) ∧ (p1 ∨ p5)) → p2) ∨ ((True ∧ False) → False))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301379527412150898916838618841 : (False ∨ (((True ∧ p2) ∨ (p3 ∨ p5)) ∨ ((p2 ∨ ((p1 → (p5 → ((p4 → (p4 ∧ p5)) ∨ p2))) ∨ p5)) ∨ (((False ∧ p5) ∨ p4) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111517623048693506507831568306 : (((p5 → ((True ∧ ((p4 → p4) ∨ p1)) ∧ (((p2 ∨ p2) → ((p1 ∧ (True ∧ True)) ∧ ((p5 ∨ p4) ∨ True))) ∨ p2))) ∧ p1) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356856863678413777517250477971 : (p5 → (((p4 ∧ p3) ∨ (p3 → p2)) ∨ (((p1 ∨ ((p1 ∧ ((p1 ∧ p4) ∧ ((p2 ∧ p3) → p4))) ∨ p4)) ∨ False) ∨ (p4 → (True ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712960727268743610379454139744 : ((((p1 ∧ ((p1 → (p2 → p4)) ∨ p5)) ∨ ((p4 ∧ p2) → (p1 ∨ (True → ((p5 ∧ ((p3 ∨ p1) ∧ False)) ∨ (p5 → (True ∨ p5))))))) ∨ p3) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167940356875058053624507306669 : (((p1 ∨ (p3 → ((True ∨ (p4 ∨ p4)) → p3))) ∨ (((p4 ∨ (p5 ∨ p1)) ∨ p3) → False)) → (((p3 → ((p1 → False) → p1)) ∧ p4) ∨ True)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62878648368773761296678167521 : ((p4 ∧ ((False → (True ∨ p1)) → (False ∧ ((((False ∨ ((p4 ∨ p2) ∧ (((p5 ∨ p2) → (False ∧ p5)) ∧ p3))) ∨ False) → True) ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41545351078337351452027424572 : ((((False ∧ (((p3 ∨ False) ∨ p3) ∨ (p3 ∧ (p1 ∨ False)))) ∨ ((p5 → p5) ∨ (p3 ∧ (((False → False) ∧ (p1 → False)) → p4)))) ∨ p1) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346183354047637358862780161086 : (p3 → (((p2 → ((p1 ∧ p1) → (p5 ∨ (((((True ∨ p2) → ((False → p4) ∧ (p1 ∨ False))) ∨ p3) → False) ∧ p4)))) ∨ True) ∧ (p3 ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193700041788838487421199533825 : ((p1 ∧ (p1 ∨ ((p1 ∧ False) ∨ ((True → p1) ∨ p5)))) → ((p2 ∨ (((p5 → p2) ∨ True) ∨ (p1 ∨ (p1 → (p5 → (p3 ∨ p5)))))) ∨ True)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
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
theorem thm_5_vars_806212041608485082802571370030 : (((p4 → (((p3 ∨ ((((p2 → (((((p2 ∧ p3) ∨ False) → p4) ∨ p5) → p3)) ∧ p3) → ((p1 ∨ p5) ∧ True)) → p3)) → False) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777915625548699538242582402960 : (((p1 ∨ ((False ∧ (True → True)) ∧ (p5 ∨ ((p3 ∧ (p3 → (p4 → (p1 ∧ ((p5 ∧ False) → ((True ∧ True) ∨ False)))))) ∧ (p1 ∨ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349746957234188887580026825131 : (p4 → (((p5 ∧ ((p3 → p1) → (p1 → p5))) ∨ (p4 ∨ ((((p4 ∨ (p5 ∧ p3)) ∧ p3) ∧ (((p1 ∧ p1) → p2) ∧ False)) ∨ True))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307447616928621518784593459062 : (p1 ∨ (p5 ∨ (((p5 ∨ (p3 ∨ ((False → False) ∨ (p2 → True)))) → False) → ((False ∨ ((True ∨ ((p5 → p2) ∧ p1)) ∨ p4)) ∧ (p1 ∨ p5))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 ∨ (p3 ∨ ((False → False) ∨ (p2 → True)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198528737064146753864270980893 : ((False ∨ ((p2 → (p3 ∨ p4)) ∧ (p1 ∧ p5))) ∨ ((p2 ∨ True) ∨ (p3 ∨ ((False ∨ ((p5 ∨ False) ∨ p3)) ∨ (((p3 → p3) ∨ p3) ∧ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161431472320358591652847862298 : ((p2 ∧ (((((p2 ∨ p2) ∨ p4) ∨ p3) ∨ (True ∨ p2)) → (((p1 ∨ (False → True)) ∧ p5) ∧ p2))) → (((p4 ∧ p4) → (p3 ∧ p3)) ∨ p2)) := by
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
theorem thm_5_vars_234305111428410373314224945019 : ((p1 → (False ∧ True)) → (((((False ∧ p3) ∨ (((True → p2) ∧ p5) → (p1 ∨ (p2 → True)))) ∧ ((p5 ∨ (p1 → p4)) → p1)) ∧ p2) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_717574729657171585604224509284 : ((((p3 → (p2 → (True → True))) ∧ (((p5 → p1) → ((((p1 ∧ (p2 ∨ False)) → p3) → ((p4 ∧ p3) ∧ (False → True))) → p3)) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234277319313436118135653884208 : ((False → (p2 → True)) → (((False ∨ ((p4 → p1) ∨ False)) ∨ (p4 → (False ∨ p5))) ∨ ((p2 ∨ (p5 ∨ (p3 ∨ p1))) ∨ ((False → p3) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124093967609809956137071649653 : (((((p4 ∧ (((p4 ∧ p1) → p1) ∨ p4)) ∧ p4) ∨ p1) ∧ ((p3 ∧ (((p2 → p4) → p1) → p3)) ∧ (p3 ∨ (p5 ∧ p3)))) → (False ∨ p3)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h3.left
      let h11 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h10.left
      let h13 := h10.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h14
      case inr h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h15.left
        let h17 := h15.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h17
    case inr h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h3.left
      let h20 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h21 := h19.left
      let h22 := h19.right
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h23 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h23
      case inr h24 =>
        -- Conjunctions on the left can always be decomposed.
        let h25 := h24.left
        let h26 := h24.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h26
  case inr h27 =>
    -- Conjunctions on the left can always be decomposed.
    let h28 := h3.left
    let h29 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h30 := h28.left
    let h31 := h28.right
    -- Disjunctions on the left can always be decomposed.
    cases h29
    case inl h32 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h32
    case inr h33 =>
      -- Conjunctions on the left can always be decomposed.
      let h34 := h33.left
      let h35 := h33.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h35



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300060800636281106280966181136 : (False ∨ ((((((True ∨ (True → ((p3 ∨ p3) ∨ (p2 ∧ ((p1 → p3) ∨ p1))))) ∨ (False → True)) → (p2 ∧ p5)) ∧ p3) ∨ p1) ∨ (True ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158033720140677537388942012987 : (((p3 → ((p1 → (p4 ∨ p3)) ∨ p3)) ∧ (((p1 → (p2 ∨ p3)) ∨ ((p4 ∧ p4) ∨ p5)) ∨ p2)) ∨ (p1 → ((True ∧ p2) ∨ (p4 → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136195253227957573117877029948 : ((((p4 ∧ False) → ((True ∨ p4) → p3)) ∧ (((False ∨ p4) ∧ p1) ∨ (True ∧ ((p5 ∨ ((False ∨ p3) ∨ p5)) ∨ p2)))) ∨ ((p1 ∧ p4) → p4)) := by
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
theorem thm_5_vars_150933797353523963189554219853 : (((True ∧ (((((p2 ∨ (p3 ∨ (False → p1))) ∨ False) → ((p5 → p4) ∨ p1)) ∨ (p2 ∨ p5)) ∨ True)) ∨ p3) → ((p4 → p2) ∨ (True ∨ True))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
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
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_784227245439185679215577402287 : (((p3 ∨ (True ∧ ((p2 ∨ (((p5 ∧ p1) ∨ p5) ∧ p4)) ∧ (False ∨ (True ∨ (((((p5 ∧ p3) → p4) ∨ p3) ∧ (p5 ∨ p3)) ∨ p1)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64075218967537281881281423001 : ((False ∨ ((((((p3 ∨ (False ∨ p1)) ∨ (p5 ∧ p4)) ∧ (False ∧ p5)) ∨ p5) ∨ p4) ∧ (p5 ∨ ((True ∨ p4) ∨ (True → (p4 ∨ p3)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48916296666699446553117834208 : (((((((((False ∨ True) ∨ (True ∧ p4)) ∧ (p5 ∧ ((True ∨ (p5 ∨ p4)) → True))) ∧ p4) ∨ p3) ∧ p3) ∧ p2) ∨ ((False → p3) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150199909834130103476910227748 : ((p2 → (((p5 → p1) ∨ ((p4 → p3) → ((p1 ∧ p2) ∧ (((p3 ∨ p2) ∨ p2) → p5)))) ∧ (p2 ∨ p3))) ∨ (p5 → ((p3 ∧ False) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346387775687149865256764349616 : (p3 → ((True → (((True ∨ p2) ∨ (p2 → ((p2 → p3) ∧ p5))) → (((((p5 ∨ False) ∨ (p1 ∨ True)) → False) → p2) ∨ p4))) ∨ (p4 → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h7 : ((p5 ∨ False) ∨ (p1 ∨ True)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h8 := h6 h7
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h9
  case inr h11 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h12
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h13 : ((p5 ∨ False) ∨ (p1 ∨ True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h14 := h12 h13
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51112034648543154396432404240 : (((((p2 → (((True ∧ p3) ∧ (True → (True → p5))) → ((p5 ∧ p5) → False))) ∧ p2) ∨ True) ∨ ((((True ∨ p2) → p1) → True) → True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300109645894708130986147419659 : (False ∨ (((p5 ∧ (False → ((False ∨ (True ∨ (p5 → p3))) ∧ p2))) → ((p5 ∧ ((p4 → False) ∨ ((p1 ∧ False) ∧ p5))) → False)) ∨ (False → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690380972828350880735566271868 : ((((p5 → ((((True ∨ p1) → (p1 ∨ (True ∨ ((True ∨ p3) → p1)))) ∨ p2) → p4)) ∨ ((p2 → ((p4 → (p2 ∧ p3)) ∨ False)) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47217623398622863725644127322 : (((((False → ((False ∨ (p4 → (True ∨ p3))) → p3)) ∨ p1) → ((p3 → (p2 → (((False ∨ p5) ∨ p1) ∧ p3))) ∨ p2)) ∨ (p4 → p4)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64532830752158569080099450400 : ((p1 ∨ ((True ∧ ((((False ∧ p5) → p4) ∨ False) → p5)) ∨ ((p4 ∨ (False ∧ (((p5 → p2) → (p2 → (p5 ∧ True))) ∨ p3))) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264251808365023681594938022316 : (True ∧ (((((p1 ∧ p2) ∧ True) ∧ p5) ∧ False) ∨ ((((p5 → ((p4 → False) ∨ (True ∨ (p3 ∧ (p1 → True))))) ∨ p3) ∨ (p1 ∨ False)) ∧ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219548150954562484353395513101 : ((p5 ∨ (p5 → (p5 → p4))) → ((((((True ∧ p1) ∨ p3) → (((False → p5) → True) → (False ∨ True))) ∧ True) → (p5 ∨ (False ∨ False))) → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : ((((True ∧ p1) ∨ p3) → (((False → p5) → True) → (False ∨ True))) ∧ True) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h12 := h2 h5
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- False on the left can always be used.
        apply False.elim h15
      case inr h16 =>
        -- False on the left can always be used.
        apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_88233315071376073724572436474 : (((True ∨ ((True → p5) ∨ p5)) ∧ (p5 ∧ (((((p2 ∧ p3) ∧ p4) ∧ (False ∧ (p3 ∧ (p1 ∧ p3)))) ∨ ((p4 → p4) ∨ True)) → p1))) → p1) := by
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
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : ((((p2 ∧ p3) ∧ p4) ∧ (False ∧ (p3 ∧ (p1 ∧ p3)))) ∨ ((p4 → p4) ∨ True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h8 := h6 h7
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h3.left
      let h12 := h3.right
      -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
      have h13 : ((((p2 ∧ p3) ∧ p4) ∧ (False ∧ (p3 ∧ (p1 ∧ p3)))) ∨ ((p4 → p4) ∨ True)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h12, we can now drive its conclusion.
      let h14 := h12 h13
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h3.left
      let h17 := h3.right
      -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
      have h18 : ((((p2 ∧ p3) ∧ p4) ∧ (False ∧ (p3 ∧ (p1 ∧ p3)))) ∨ ((p4 → p4) ∨ True)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h17, we can now drive its conclusion.
      let h19 := h17 h18
      -- One of the premise coincides with the conclusion.
      exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351530261963275197739942182434 : (p4 → (((p1 → (((p3 → True) ∨ False) → ((p4 → p2) ∨ (p1 → p5)))) ∨ (True ∨ (p5 → p1))) ∨ (False ∧ (False → (False ∨ (False ∨ p4)))))) := by
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
theorem thm_5_vars_256015644122644800523703236265 : ((True ∨ p3) → (p2 ∨ (p4 ∨ ((((p3 ∨ p4) → (True ∧ p5)) → (p3 ∨ True)) ∨ (p5 ∨ ((p3 → p3) → (True → (True ∨ (p3 → False))))))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137230566232602500067249548265 : ((p1 ∧ ((p5 ∧ ((False ∨ (p2 ∨ (((((p3 → p1) ∨ p3) ∧ (True → False)) ∨ p1) → (False ∧ p2)))) → p3)) → p4)) ∨ ((True ∨ p2) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206337781464174792893851876232 : ((p2 ∨ (((p3 → True) → False) ∧ p2)) ∨ (p3 → (p2 → (((p1 ∧ False) → (((p4 → p3) ∧ False) ∧ (False → ((p4 ∨ p4) ∧ p5)))) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h3.left
  let h8 := h3.right
  -- False on the left can always be used.
  apply False.elim h8
  -- Implications on the right can always be decomposed.
  intro h9
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h9
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682793874904425391794627529071 : (((((p3 ∧ (p3 ∨ False)) ∧ (p3 → (p4 ∨ (p3 → (p4 ∧ (True → ((True ∧ True) ∧ p3))))))) ∧ (p5 ∧ (((p1 ∧ p3) ∧ False) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



