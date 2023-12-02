variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194595178383206990036419066964 : (((((p3 → (True ∨ p5)) → False) ∨ p5) ∨ True) ∧ ((((p2 → False) ∨ p1) ∨ ((((p2 → p5) ∨ ((True ∨ p1) → p5)) → True) ∨ p2)) ∨ p3)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198746049742613201257456571070 : ((True → ((p2 ∨ (p5 ∨ (p1 ∧ False))) ∨ p1)) ∨ ((((True ∨ True) ∧ (True ∧ False)) → (True ∨ p4)) ∨ ((p5 → (p2 → (True ∧ p5))) ∨ p1))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617695900243818829359872214402 : (((((((True ∧ p2) ∧ p4) → (p3 ∨ p3)) ∨ ((((p5 ∨ p2) ∧ p2) → p1) → ((p2 ∧ p1) ∨ ((False ∧ p1) ∨ (p2 → p2))))) ∨ p3) ∨ p1) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167482414631440047607974655163 : ((((False ∨ (p3 ∨ (p2 ∨ ((p5 → (p2 ∧ False)) ∨ (p5 ∨ p5))))) ∧ p4) ∧ (p1 → p2)) → (((p1 ∨ p1) ∧ (p3 ∨ False)) ∨ (p4 → True))) := by
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
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h12
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h15
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h16 =>
          -- Disjunctions on the left can always be decomposed.
          cases h16
          case inl h17 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h18
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h19 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h20
            -- True on the right can always be proven directly.
            apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213659959544263921963381659853 : ((((True → False) ∨ p3) ∨ False) ∨ (p2 ∨ ((p3 ∨ ((p5 → ((p1 → (True → ((p3 → ((True ∨ p3) → False)) → p1))) ∨ False)) ∧ True)) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56934934667450403619393294411 : (((False ∨ (True ∨ False)) ∧ (p5 ∧ (((((p4 ∨ ((((p4 ∧ False) → p4) ∨ p2) ∨ p3)) ∧ (p4 → p1)) ∧ p1) ∨ (False ∧ p3)) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205592600696508097655533135445 : (((p3 → p4) ∧ (p5 → (False ∧ p1))) ∨ (p4 ∨ (p4 → (((p1 ∨ p2) → (((p5 → p3) ∧ p1) → p4)) ∨ ((True → p4) → (p5 ∧ False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_660098880394789126944097870607 : ((((((True ∧ (p5 ∧ (p1 ∧ ((((True ∧ True) ∨ False) ∨ p5) ∨ ((p3 ∧ p2) → p2))))) ∨ (p4 ∧ (False ∧ p1))) ∨ p5) → (p4 ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657631119276949746574873258241 : (((((True ∨ p3) → ((p1 ∧ True) ∨ (p5 ∨ (p1 ∨ (((p2 ∨ p4) → (False → False)) ∨ (((p4 ∨ p3) → p3) → p4)))))) ∨ (False → p5)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193572830417501444526371705147 : (((p3 ∨ True) → (True ∧ ((False ∧ (p3 ∨ p1)) ∧ False))) → ((((p3 ∨ (p1 ∧ p1)) ∨ p2) → p5) ∧ ((p1 ∨ (p1 ∧ p2)) ∨ (p1 ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h5 : (p3 ∨ True) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h6 := h1 h5
      -- We need to get the right conjuct of h6 based on <expert-advice>.
      let h7 := h6.right
      -- We need to get the right conjuct of h7 based on <expert-advice>.
      let h8 := h7.right
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h12 : (p3 ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h13 := h1 h12
      -- We need to get the right conjuct of h13 based on <expert-advice>.
      let h14 := h13.right
      -- We need to get the right conjuct of h14 based on <expert-advice>.
      let h15 := h14.right
      -- False on the left can always be used.
      apply False.elim h15
  case inr h16 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h17 : (p3 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h18 := h1 h17
    -- We need to get the right conjuct of h18 based on <expert-advice>.
    let h19 := h18.right
    -- We need to get the right conjuct of h19 based on <expert-advice>.
    let h20 := h19.right
    -- False on the left can always be used.
    apply False.elim h20
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h21 : (p3 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h22 := h1 h21
  -- We need to get the right conjuct of h22 based on <expert-advice>.
  let h23 := h22.right
  -- We need to get the right conjuct of h23 based on <expert-advice>.
  let h24 := h23.right
  -- False on the left can always be used.
  apply False.elim h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_195709159817679114842487522931 : (((False ∨ True) ∨ (p3 ∧ ((p5 ∧ True) ∨ p5))) ∧ ((True → p2) → (((p5 → ((p1 ∧ p1) ∨ (p5 → (p2 → False)))) ∧ p5) ∨ (False → p2)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214835756072551706010755322899 : (((p5 ∨ p1) ∨ (p5 → p4)) ∨ (((p1 ∧ p3) → (False ∧ False)) ∨ (((p1 ∧ (True ∨ (((p1 ∨ p4) ∧ p4) → (False → p4)))) ∧ p1) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321257412757669096140245917965 : (p4 ∨ (p4 ∨ ((((p5 ∧ p4) ∧ (p3 → p1)) ∨ (False ∨ p5)) → ((p4 ∨ (p4 ∧ p3)) ∨ (False → ((False ∧ p3) ∨ (p4 ∨ (p2 ∨ False)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- False on the left can always be used.
      apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307446395891859373892177429936 : (p1 ∨ (p5 ∨ ((((True ∧ (p3 ∧ p5)) ∧ (p1 ∨ True)) → ((p4 ∧ p2) ∨ p1)) → (p3 → ((p1 ∨ p4) → ((False ∧ p4) ∨ (p4 ∨ p3))))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171792322292625236253978812732 : (((((p1 ∨ False) ∨ ((p2 ∨ ((p4 → p3) ∧ p2)) → p3)) → (p3 ∧ False)) → False) ∨ ((p3 ∨ ((((p3 ∧ p2) ∧ p1) → True) ∧ False)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207902192022865158508341317243 : (((p1 ∧ (p3 ∧ p2)) ∧ (p2 → p5)) → ((((p4 ∨ (False → ((p4 → False) ∧ p2))) ∧ (p4 → (p2 ∧ p5))) → False) ∨ (p3 → (p5 ∧ p3)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h8
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h9 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h10 := h3 h9
  -- One of the premise coincides with the conclusion.
  exact h10
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353533760785148510284741242030 : (p4 → (p3 ∨ ((((False ∨ p2) ∨ (((True ∧ p5) → True) → (p2 ∨ p4))) → (((True ∧ (p2 ∨ p3)) ∧ (True ∨ (True → p4))) ∧ p3)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50741809030363647278510472009 : (((p1 ∧ (p5 ∧ ((((False → p1) ∨ p1) → ((p1 → p4) ∧ (p2 ∨ (p1 ∨ True)))) ∧ (p5 ∧ p4)))) → ((p5 ∨ False) ∧ (p2 ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_643564684954212881512140030900 : ((((p4 ∧ ((p3 → False) → ((p1 ∨ p2) → (False → ((p1 → ((((p1 ∨ False) ∧ p2) ∨ p1) ∧ ((p4 ∨ True) ∧ p5))) ∨ p3))))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40209878003822822901030974579 : (((((p4 ∨ p3) ∨ ((((p5 ∨ p1) ∧ p3) ∧ (p4 → (((p4 ∧ (False → ((p5 → p3) → p3))) ∨ p4) ∧ p2))) ∧ p3)) ∧ p3) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313013277767318087852089179395 : (p3 ∨ (((((p2 ∧ p1) → p5) ∧ ((((((True ∨ (p4 ∨ p4)) → p3) ∨ p4) ∧ (p4 ∧ p2)) ∨ False) ∨ (p3 ∧ (p1 → True)))) ∨ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258633620834081645005242294064 : ((p5 ∨ p4) → (p4 → ((((((True → ((p4 ∨ p2) → (p4 → ((p4 → p4) ∨ (p2 ∧ False))))) → p3) → (p2 ∧ p2)) ∨ p2) ∨ p3) ∨ p4))) := by
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
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615108711683151747994175707534 : ((((((((((p2 ∧ (p2 ∨ True)) ∨ (p3 ∧ (p3 ∧ p3))) ∨ p2) ∧ p1) ∧ p5) ∨ p1) ∧ (p3 ∨ (p4 → ((p1 → True) ∧ p1)))) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_24719080720686673413651788761 : ((((False ∧ p3) ∧ p2) ∨ ((((((p3 ∧ True) ∧ p1) ∧ (p4 → p1)) ∨ (p2 ∧ False)) ∨ ((((p1 ∧ p1) ∨ p2) ∨ False) → True)) ∨ False)) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178108364140002936658556506682 : ((((True ∧ (p4 ∧ (False ∨ (p3 ∨ (True → p5))))) ∨ (p3 → p3)) → p4) ∨ ((False ∨ ((True → p1) → (((p1 ∧ p5) ∧ p5) → p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252273444502506722506182163718 : ((p4 → p5) ∨ (((p1 ∨ p2) ∧ ((((p3 ∧ (False → (((p5 ∧ p5) ∧ (True ∧ False)) → False))) → p3) → False) ∧ ((True → p4) ∨ p4))) → False)) := by
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
    let h5 := h3.left
    let h6 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h8 : ((p3 ∧ (False → (((p5 ∧ p5) ∧ (True ∧ False)) → False))) → p3) := by
        -- Implications on the right can always be decomposed.
        intro h9
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- One of the premise coincides with the conclusion.
        exact h10
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h12 := h5 h8
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h14 : ((p3 ∧ (False → (((p5 ∧ p5) ∧ (True ∧ False)) → False))) → p3) := by
        -- Implications on the right can always be decomposed.
        intro h15
        -- Conjunctions on the left can always be decomposed.
        let h16 := h15.left
        let h17 := h15.right
        -- One of the premise coincides with the conclusion.
        exact h16
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h18 := h5 h14
      -- False on the left can always be used.
      apply False.elim h18
  case inr h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h3.left
    let h21 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h22 =>
      -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
      have h23 : ((p3 ∧ (False → (((p5 ∧ p5) ∧ (True ∧ False)) → False))) → p3) := by
        -- Implications on the right can always be decomposed.
        intro h24
        -- Conjunctions on the left can always be decomposed.
        let h25 := h24.left
        let h26 := h24.right
        -- One of the premise coincides with the conclusion.
        exact h25
      -- We have shown the premise of h20, we can now drive its conclusion.
      let h27 := h20 h23
      -- False on the left can always be used.
      apply False.elim h27
    case inr h28 =>
      -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
      have h29 : ((p3 ∧ (False → (((p5 ∧ p5) ∧ (True ∧ False)) → False))) → p3) := by
        -- Implications on the right can always be decomposed.
        intro h30
        -- Conjunctions on the left can always be decomposed.
        let h31 := h30.left
        let h32 := h30.right
        -- One of the premise coincides with the conclusion.
        exact h31
      -- We have shown the premise of h20, we can now drive its conclusion.
      let h33 := h20 h29
      -- False on the left can always be used.
      apply False.elim h33



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47067604046159582579223254197 : (((((p5 ∧ p5) ∨ (((p5 → p4) ∧ ((p4 ∧ (p4 ∨ p3)) ∧ p1)) ∨ ((p4 ∧ (p4 → p5)) ∨ False))) ∨ (False → True)) ∨ (False ∨ p2)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116809140215248243121282256603 : (((p3 ∨ p3) ∨ (p1 ∧ (p2 ∧ (p3 ∨ ((((True → ((False ∨ True) ∨ p1)) → False) → (p3 ∧ p1)) ∨ ((True ∧ p5) ∧ p2)))))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336156231058988755061846656310 : (p1 → ((((p2 → (p2 ∨ (((((((p2 ∨ True) → (p4 → (True ∨ False))) → p3) → True) ∨ p1) → p4) → False))) ∧ (p4 ∨ p5)) → False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684710917422712071002169792174 : (((((p3 ∧ p2) ∧ ((p5 ∨ (((p4 ∨ False) → (p5 ∧ ((False ∧ p3) ∨ p3))) → p3)) ∧ False)) ∨ (p2 ∧ (p4 ∧ (p2 ∧ (p2 → True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232289808302270996114259286425 : (((p2 → p5) → p3) → ((True ∧ ((p4 ∧ (((p5 → False) ∨ (p2 ∨ True)) ∨ (p3 ∨ (False ∧ (p2 → p1))))) ∧ (p3 → p1))) ∨ (True ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263207020434974199107664914175 : (True ∧ ((((p4 ∧ (((((False → p2) ∧ p1) ∨ (p5 ∧ (p4 → p5))) ∧ (True ∧ (True ∧ p4))) ∧ (True → p1))) ∨ p3) → p3) → (p2 → p2))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612764080136895735841592185337 : (((((((p3 → p4) → p1) ∧ ((p3 ∨ (((True ∧ p1) ∧ True) → ((p4 ∨ ((p5 → True) ∧ False)) ∨ False))) ∧ p5)) ∨ (p2 ∨ p3)) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_148048282291181478183714111933 : (((p4 ∧ (((p4 ∨ (((False ∨ p4) → (p2 → (p5 ∨ p1))) ∨ (p3 ∧ p1))) ∧ p1) ∧ p1)) ∨ (p2 ∨ p3)) ∨ (((False ∨ False) → p5) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136374515255026705925528470619 : ((((p2 ∧ (True ∧ p4)) → p5) ∨ (p2 ∧ ((p2 ∨ (False ∧ p2)) → ((p4 ∨ ((p3 → (p4 → p3)) → p5)) ∧ p3)))) ∨ (p3 → (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711860421654130344245248884110 : (((((p2 ∧ (p4 → (p2 ∧ p1))) ∧ p2) ∨ (((p3 ∧ p2) ∨ p1) → ((p3 → (False ∧ (((True → p4) ∨ p5) ∧ False))) ∨ (False → p2)))) ∨ p3) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227690138455811615260914067835 : ((p1 ∧ (True ∧ p3)) ∨ (((p3 ∨ (p5 ∨ ((((p1 ∧ (p1 ∨ True)) ∨ (p5 ∧ (p4 ∧ False))) ∨ True) ∨ True))) ∨ p4) ∨ ((p3 ∧ p4) → p3))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114589798631847989326474440150 : ((((p1 ∧ p1) ∧ (p4 ∨ (True → (False ∧ (((p3 → p3) ∧ p4) → (p2 ∧ p1)))))) ∧ (((True → p5) ∧ (p3 → p1)) ∧ True)) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204177977291818521255410407378 : ((((p2 ∨ (p4 ∨ p3)) ∨ p3) ∧ False) ∨ (((p4 ∧ (p5 → p4)) ∨ ((p3 ∨ True) ∧ p4)) → (p3 ∨ ((p5 ∧ p5) ∨ ((p5 ∨ True) → p4))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h15 =>
        -- One of the premise coincides with the conclusion.
        exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207984826196154825389933099758 : ((((p1 ∧ False) ∨ p3) ∨ (p1 → p3)) → (p3 ∨ (p4 → (p4 ∧ (p5 ∨ ((p3 → (p4 → (((p1 ∨ p5) ∧ False) ∨ False))) ∨ (p1 → p4))))))) := by
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
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h8
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174882869390723185159279401728 : (((p5 → p3) ∨ (p3 → ((p4 → p3) ∨ (p3 ∨ ((p2 ∨ p1) ∧ (True ∨ p4)))))) → (p1 ∨ ((p4 ∨ p5) ∨ (True ∧ (p4 → (False ∨ p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_640961242137596482606209099660 : (((((p1 ∧ True) ∨ ((p4 ∨ ((False ∨ (p2 → False)) → (p1 → (((((p3 ∨ True) ∨ p3) → p1) ∧ (p1 ∧ p5)) ∨ p3)))) ∧ True)) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118575997078345453626513062663 : ((p4 ∨ (((True → (p4 ∧ ((True ∧ p1) ∨ ((p5 → ((p4 ∨ p3) ∨ p1)) → p5)))) ∧ (p2 ∨ (p5 → (p4 → p3)))) ∨ p1)) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209590192833441361012622954011 : ((p5 → (True → (p1 ∧ (p2 ∨ p3)))) → (((p1 ∨ p2) → ((p2 → False) ∧ ((False → p3) → p1))) ∨ ((((p3 → True) ∨ p2) ∧ p5) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351475195995826385599963127119 : (p4 → ((p2 → ((((p5 ∧ (p2 ∨ p3)) → (p5 ∨ ((p1 → p4) ∨ p3))) ∨ (True ∧ (p4 ∨ p4))) ∨ p2)) → ((p3 → False) ∨ (p4 ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_685953271311260211991413432695 : (((((True ∧ (p3 → (p4 ∧ ((p2 ∨ (p4 → ((True → p1) ∨ p2))) ∧ p5)))) ∧ (p3 → p1)) → (((False → False) ∧ (p5 ∧ p4)) → p4)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h7.left
  let h10 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181623872350814158100173857752 : ((p2 → (False ∧ (((p1 ∨ (p3 ∨ ((True ∧ p2) → True))) ∨ False) → False))) → (((((p2 ∨ p3) ∧ p3) ∨ p5) ∧ ((p2 → p3) → p1)) → p1)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h9 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h8
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h10 := h1 h9
      -- We need to get the left conjuct of h10 based on <expert-advice>.
      let h11 := h10.left
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h13 : (p2 → p3) := by
        -- Implications on the right can always be decomposed.
        intro h14
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h15 := h4 h13
      -- One of the premise coincides with the conclusion.
      exact h15
  case inr h16 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h17 : (p2 → p3) := by
      -- Implications on the right can always be decomposed.
      intro h18
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h19 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h18
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h20 := h1 h19
      -- We need to get the left conjuct of h20 based on <expert-advice>.
      let h21 := h20.left
      -- False on the left can always be used.
      apply False.elim h21
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h22 := h4 h17
    -- One of the premise coincides with the conclusion.
    exact h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59040933177936107804662725728 : (((p4 ∧ p2) ∨ ((p4 ∨ ((((((True ∨ True) → False) ∨ (p2 ∨ False)) ∨ (((p5 ∨ p2) ∧ p5) ∨ p3)) → (p3 ∨ p1)) → p2)) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158774144308337607772243588315 : ((p4 ∧ (p5 ∨ ((((p3 ∧ p2) → p2) ∧ (True → p5)) → (p2 ∧ ((p3 ∨ (p4 ∧ p4)) ∧ p1))))) ∨ (True ∧ (True ∨ (p3 → (p2 ∧ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316914956867611976319179773901 : (p3 ∨ (p2 → ((True ∧ (((p4 ∧ (p5 ∧ (((((p4 ∨ False) ∨ (p5 ∧ True)) ∨ p4) → (p1 ∨ p4)) → (True → p4)))) ∨ True) ∨ p1)) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_706516761986507330311480466768 : ((((p5 ∨ (p3 ∧ (((p4 → p5) ∧ p2) ∧ p2))) ∧ (p2 ∧ (((((p5 ∧ (False ∨ p3)) ∨ p3) → p1) → ((p4 ∨ False) → p1)) ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310251959735842918593683610632 : (p2 ∨ ((False ∨ (((p4 → p5) ∧ (((p1 ∨ p3) → True) ∨ p3)) ∧ p2)) → (((True → p5) ∨ (p3 ∨ (p3 ∨ p3))) → (p4 ∨ (True ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h4 =>
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
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
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h14 =>
        -- False on the left can always be used.
        apply False.elim h14
      case inr h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h15.left
        let h17 := h15.right
        -- Conjunctions on the left can always be decomposed.
        let h18 := h16.left
        let h19 := h16.right
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h21 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h22 =>
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h23 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h24 =>
          -- False on the left can always be used.
          apply False.elim h24
        case inr h25 =>
          -- Conjunctions on the left can always be decomposed.
          let h26 := h25.left
          let h27 := h25.right
          -- Conjunctions on the left can always be decomposed.
          let h28 := h26.left
          let h29 := h26.right
          -- Disjunctions on the left can always be decomposed.
          cases h29
          case inl h30 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h31 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
      case inr h32 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h33 =>
          -- False on the left can always be used.
          apply False.elim h33
        case inr h34 =>
          -- Conjunctions on the left can always be decomposed.
          let h35 := h34.left
          let h36 := h34.right
          -- Conjunctions on the left can always be decomposed.
          let h37 := h35.left
          let h38 := h35.right
          -- Disjunctions on the left can always be decomposed.
          cases h38
          case inl h39 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h40 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655313028332809451887823863861 : (((((p2 ∨ (((p3 → (False ∨ p2)) ∨ False) ∨ (p2 ∧ ((((True ∨ p2) ∨ (False → p5)) ∧ p1) → p5)))) ∧ (p2 ∨ False)) ∨ (p1 → True)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_709221186898459910005720382301 : (((((p4 → p3) ∧ ((p2 ∧ (p4 ∧ p2)) → p3)) → (p3 ∨ (p5 ∨ (p3 ∨ (p5 ∧ (((p1 ∨ ((p4 ∧ p2) ∧ p4)) ∧ p4) → p1)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166676281902060680045644054316 : ((p2 → (((((False → (False → p2)) ∧ (p5 ∨ p3)) ∧ p5) ∨ (p1 ∧ p5)) ∨ (p1 ∧ p1))) ∨ ((((p1 ∧ p1) ∨ p5) ∨ p1) ∨ (False → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172208751370186167433803771735 : (((((p4 ∨ p3) → p5) ∧ (True → ((p2 → p1) → p2))) → (p5 → (False ∧ False))) ∨ (((True → p4) ∨ (False → p4)) ∨ ((p2 → False) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111811650067450504359380593869 : (((((p5 ∨ p1) ∧ ((((p5 → (p4 → p5)) → p2) → (((p4 ∧ (False → p4)) ∧ p3) ∨ p4)) ∨ p4)) → (True ∧ p1)) ∨ p4) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116998900916225209679292847125 : (((True ∨ p5) → ((p2 → ((p1 ∧ ((((p2 → p3) → (p5 ∨ p1)) → True) ∨ (p5 → (p3 → p5)))) ∨ (p2 ∧ False))) → p3)) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123119229672240868210139063264 : ((((p2 ∧ (True ∧ (((p4 ∨ False) ∧ (True → False)) ∧ False))) ∧ (((True ∧ True) ∧ (p3 → p5)) ∧ True)) → (p2 → (False ∧ p1))) → (p5 ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259110677065436241333451356903 : ((True → p5) → (False ∨ ((p1 ∨ ((p5 → (((p3 → (True → (False ∧ (False ∨ ((False → p3) ∨ p5))))) → p4) → (p5 ∧ p1))) ∨ p5)) ∨ p2))) := by
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264792493906961901443653230280 : (True ∧ ((False ∧ p3) ∨ ((p5 ∧ ((p3 ∧ p3) ∧ p2)) → (((False ∧ (p2 → (p1 ∨ False))) ∨ (True → p3)) ∨ (p4 ∧ ((p3 → p2) → True)))))) := by
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
  let h6 := h4.left
  let h7 := h4.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h8
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137821943347172905902901001751 : ((p3 ∨ ((((((p1 ∧ (((p4 → p3) → p3) → p4)) ∧ ((p2 ∨ False) ∧ p3)) → (True → p1)) ∧ p4) → p4) → p1)) ∨ (p4 → (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112663543326662971953341256073 : ((((((((p1 ∨ p1) ∧ False) ∨ (True ∧ p4)) ∨ ((p3 ∧ p2) ∧ p4)) → (p1 ∧ (p5 ∧ p3))) ∨ (p4 ∨ (p4 ∨ p5))) → p4) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171597426708163708182704953258 : (((((p2 → ((p3 → True) → p1)) ∧ False) ∧ (True → ((p3 ∨ p5) ∨ False))) ∨ True) ∨ (False ∨ ((p3 ∧ (((True ∨ p1) ∧ True) ∧ p3)) ∨ p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206037762479674948880065171820 : ((p2 ∧ (p1 ∧ ((p3 ∧ p4) ∨ p2))) ∨ (p3 ∨ ((p1 → (p5 → (True → (((True ∨ (p5 → (True ∨ p3))) ∧ p1) → (p4 → p5))))) ∨ p5))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214628007153176398977950783728 : (((False → p3) ∧ (True ∧ p5)) ∨ ((p5 → ((((p5 ∧ p4) ∨ (True ∨ p2)) ∧ ((False ∨ p2) ∨ False)) ∨ ((p5 ∧ p2) → (p2 ∨ p1)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39333192692660661758359723929 : (((p2 ∧ (((p4 ∨ p3) ∨ (((p5 → p1) → p4) → (p3 ∨ p4))) → ((False → ((False → (True → p5)) ∨ p5)) ∧ (p2 → p3)))) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67300723152395358013137209369 : ((p1 → (((((((False ∧ (p4 ∧ False)) ∨ True) → p1) ∧ p5) ∨ (False ∧ p5)) → ((p5 ∧ ((p5 ∨ p3) ∨ True)) ∧ (p4 ∨ p2))) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184904358794422689722345862117 : ((((p1 ∧ p4) ∨ False) ∨ (True ∧ (((p5 → False) → p3) ∧ p1))) ∨ (((((p4 → ((True ∨ p3) ∧ p1)) ∨ (p4 ∨ p4)) ∧ False) → p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_714979292169268259966699735484 : ((((False ∨ ((p4 → (p2 ∧ True)) ∨ p2)) → (((((((False ∧ p4) ∧ False) ∨ True) ∨ ((False ∨ p5) ∧ p3)) ∧ p2) → p4) → (p2 ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612495436487592124897301745251 : ((((((((p4 ∨ p2) ∧ ((((p5 → p1) ∧ p3) → ((False → p1) → p3)) ∧ ((p5 → p3) ∧ False))) ∧ False) ∨ True) ∨ (p5 ∨ True)) ∨ p5) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58750005108668972967507374064 : (((p4 → True) ∧ (((((((p1 ∨ p1) → p5) → (p5 → (p5 ∧ p5))) ∧ p1) → p2) → ((True → p3) ∨ (p4 ∨ p4))) → (p5 ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_891880641753459996559208979132 : ((((((p3 → p1) → ((False ∧ p2) ∧ (p2 ∧ (p1 → ((((True → p1) → False) → (p3 ∨ p3)) ∨ False))))) ∧ p2) ∧ ((p2 → p3) → p1)) → p5) ∧ True) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : (p3 → p1) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h8 : (p2 → p3) := by
      -- Implications on the right can always be decomposed.
      intro h9
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h10 := h3 h8
    -- One of the premise coincides with the conclusion.
    exact h10
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h11 := h4 h6
  -- We need to get the left conjuct of h11 based on <expert-advice>.
  let h12 := h11.left
  -- We need to get the left conjuct of h12 based on <expert-advice>.
  let h13 := h12.left
  -- False on the left can always be used.
  apply False.elim h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_685212267307533047464288464733 : ((((True → (((((p4 ∧ (((p3 ∧ p3) ∧ (p3 → True)) → p3)) ∨ True) ∧ p1) → p3) ∨ False)) ∨ (False → (p4 ∨ ((p2 ∨ True) ∨ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39654832696949080654005858378 : (((p3 ∨ ((p2 ∨ p1) ∨ ((p2 ∧ (p5 ∧ (p4 ∨ ((p3 ∨ p2) ∨ (p3 ∧ (((False ∧ p2) ∧ p4) ∨ False)))))) ∧ (True ∧ p4)))) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678267225736695183181150199152 : ((((((False → (False → p4)) → (p5 ∨ (p2 ∧ p1))) ∧ ((p3 ∨ ((p5 ∧ False) → (False ∨ p1))) ∨ True)) ∨ (((p3 ∧ p4) ∧ p4) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114955416984275376842473306274 : (((p4 ∧ (((False → ((True ∧ (p5 ∧ p3)) ∧ p1)) → (p5 → p1)) → p5)) → (p3 → (p3 ∨ (p3 ∨ (True ∨ (p4 ∧ p2)))))) ∨ (p3 ∧ p2)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320052395373713469148149548156 : (p4 ∨ ((p5 ∧ (p5 ∧ p1)) ∨ (((True ∧ p1) → (False ∧ False)) ∨ (((True ∧ (False → (p4 → (p4 ∨ p3)))) ∧ ((p5 ∨ p5) ∨ True)) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160712698040552307141962182498 : (((((p1 ∧ p4) ∧ False) → (p4 ∨ (p5 ∧ p4))) ∨ (((p3 ∨ (p2 ∨ False)) ∨ p5) ∧ (p4 ∧ p1))) → (((p3 → p2) ∨ p4) ∨ (p1 → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h6.left
        let h10 := h6.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Conjunctions on the left can always be decomposed.
          let h13 := h6.left
          let h14 := h6.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h13
        case inr h15 =>
          -- False on the left can always be used.
          apply False.elim h15
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h6.left
      let h18 := h6.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624831946807067394553946153233 : ((((p5 ∨ ((p3 ∨ ((((True ∧ p3) ∧ (True ∨ p2)) ∨ (p4 ∧ (p2 → (p2 ∨ (p3 → (p4 ∨ False)))))) ∨ False)) ∨ (p3 ∨ p3))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135200493445734233617693592341 : ((((p4 ∧ ((True → p1) ∧ (p5 ∧ ((p3 ∧ ((False → True) → (p3 ∨ p5))) → p3)))) ∧ (True ∨ p1)) → (p1 ∨ p3)) ∨ (False → (p2 ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328535492191983548396092987266 : (True → ((p4 ∨ (((False → p3) ∨ ((p4 ∧ (True ∨ (p4 ∨ p1))) ∨ (False ∨ p1))) → p1)) ∨ ((p3 ∧ ((p5 ∧ p1) → (p3 ∧ False))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638840046864444331963836517514 : (((((((True ∨ True) → p5) ∨ p2) ∧ (p2 ∨ ((p3 → (((p4 ∧ True) ∨ ((True ∨ True) → (p2 ∨ (p3 ∧ p3)))) ∧ p4)) ∨ False))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65378005702474230377731408457 : ((p3 ∨ (((False ∨ ((p4 → (p3 ∧ p3)) ∧ True)) ∧ False) ∧ (((p2 ∨ (p2 ∧ ((p5 → True) ∨ p2))) ∧ (False → p2)) → (True → p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357075988173174305101423177394 : (p5 → (((p1 ∨ p3) ∨ p1) → (p2 ∨ ((p1 → ((((p2 ∧ True) ∨ ((p4 ∨ p2) ∨ p5)) → ((False → False) ∧ p4)) ∧ (True → p1))) ∨ True)))) := by
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
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_660147799353167373081965554633 : ((((((p1 ∨ ((p2 ∨ False) ∧ (((False ∨ False) → p1) → p4))) ∧ ((((p4 ∧ p4) ∧ (False ∨ p5)) → True) ∧ p5)) ∨ p5) → (p3 ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116239129024739039616380605425 : ((((True ∨ p5) → False) ∨ ((p1 ∧ ((((False → (p1 ∨ (p5 ∧ p2))) ∨ True) ∨ False) → (p1 ∧ True))) ∨ (p3 ∧ (p4 ∨ p3)))) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357124167817352122474505116477 : (p5 → ((p4 → (p2 → True)) → ((((p1 ∨ p1) → (((p3 ∨ ((p2 ∧ True) → ((True ∧ False) ∧ p2))) ∨ p1) ∧ p1)) ∨ (p3 ∧ True)) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690325523327463484839444184797 : ((((p2 → (False ∧ (p2 → (((((p4 → p4) ∨ p4) → (p5 ∨ p2)) ∨ p4) ∨ p5)))) ∨ (p3 ∧ (p2 ∨ (p2 ∧ ((p5 → p1) → False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245629608602519268842470126959 : ((p3 ∧ False) ∨ (p1 ∨ (((((p1 ∨ p5) ∧ (p5 ∨ (p5 → p1))) ∧ (p1 ∨ p1)) → (((True ∧ p2) ∨ (p4 → p1)) ∨ False)) ∨ (p4 ∧ True)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h8 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h9
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- One of the premise coincides with the conclusion.
        exact h10
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h13 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h14
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h15 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h16
        -- One of the premise coincides with the conclusion.
        exact h15
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h19 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h20
        -- One of the premise coincides with the conclusion.
        exact h19
      case inr h21 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h22
        -- One of the premise coincides with the conclusion.
        exact h21
    case inr h23 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h24 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h25
        -- One of the premise coincides with the conclusion.
        exact h24
      case inr h26 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h27
        -- One of the premise coincides with the conclusion.
        exact h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720382203030678530061472305896 : ((((((False ∨ p2) → False) ∨ p2) → (((p1 ∨ p5) ∨ (p5 ∧ p2)) ∧ (((p3 → p4) → ((((True ∧ False) ∨ p2) ∨ p2) ∨ p4)) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259325810268660871384048228696 : ((False → p2) → (((p1 ∨ (True → (((p2 → p4) ∧ (p2 → p2)) ∨ (((p3 ∧ p5) ∨ True) ∨ (p4 ∨ p1))))) ∨ p4) ∨ (True → (False → True)))) := by
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
theorem thm_5_vars_41990791378769652860440599695 : ((((p5 ∨ p5) ∧ (p2 → (((((p3 → (True ∨ (False → (p5 ∧ ((p2 ∨ p1) ∨ p4))))) ∨ p1) → p5) → p4) ∧ (True → False)))) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121673566654829213260978617496 : ((((((False ∧ (p2 ∧ (True ∨ p5))) → (p2 ∧ (True ∧ True))) ∧ True) → ((p2 ∨ ((p1 ∨ True) ∨ (p2 → p4))) → p4)) → p3) → (p4 → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193580155534088899730667378894 : (((p5 ∨ True) → (p4 ∨ (p5 ∨ (p5 ∨ (p1 ∨ p5))))) → ((p2 → ((p1 ∧ ((p4 ∨ True) ∨ (True ∨ (p5 ∨ (True ∨ p1))))) ∧ p1)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621135692454674539244249768887 : (((((p5 → True) → (((p1 → (p3 → p3)) → p1) ∨ (p1 → (((p3 ∧ ((True ∧ p4) ∧ (p5 ∨ False))) → (p4 ∧ False)) → p1)))) ∨ p5) ∨ p3) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48664581775700047809533275121 : ((((((p4 ∨ (False ∧ ((p4 → p3) ∧ p1))) ∨ p5) ∧ (p3 ∧ p3)) ∨ ((True ∧ (True ∧ False)) ∧ (p2 ∧ p3))) ∧ ((p2 ∧ p5) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328168675567891135050691803976 : (True → (((((((p1 → p4) → p2) ∨ (((((p3 ∧ p1) ∨ False) ∧ (p3 ∧ p5)) ∨ p5) → p3)) ∨ False) ∧ p1) → p4) → ((p3 ∧ p4) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356159902768407478756055192560 : (p5 → (((p1 ∧ (p2 → p3)) ∧ (False ∧ (p2 ∧ (((p4 → (p5 → (False ∨ p5))) ∨ p3) ∨ True)))) ∨ (p4 ∨ (False → (p5 → (p4 → p1)))))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186798450503980148030086326289 : ((((True ∧ p1) ∨ (p2 → p1)) ∧ ((True ∧ (False ∨ p3)) ∧ p3)) → ((p2 ∨ ((p2 ∨ False) ∧ (p4 ∧ p1))) ∨ ((True ∧ True) ∨ (p3 → p5)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h3.left
    let h15 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h14.left
    let h17 := h14.right
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h18 =>
      -- False on the left can always be used.
      apply False.elim h18
    case inr h19 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro



