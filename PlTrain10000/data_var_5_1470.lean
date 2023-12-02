variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60458537363554875417567712304 : (((p5 → p2) → ((p4 → (p4 ∧ ((((p4 ∨ (False ∧ p1)) ∧ ((p4 ∨ (((p3 ∧ p1) → True) ∨ p2)) → p4)) ∧ p1) ∨ p2))) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_687143416105278023626618547328 : ((((p3 → (((False ∨ False) → (False → (((p4 ∨ ((p4 → p1) ∨ True)) ∧ p3) ∨ p1))) ∧ p4)) → ((p3 ∧ (p4 ∧ p3)) ∧ (p3 ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_773757668008475717625647374947 : (((False ∨ ((((((p3 ∨ (((((False → p5) → p4) ∨ True) ∨ False) ∨ ((p1 ∧ p3) → p2))) ∨ p5) ∧ p2) ∧ p4) ∧ (p2 → p3)) → p2)) ∨ p4) ∧ True) := by
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
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Disjunctions on the left can always be decomposed.
          cases h12
          case inl h13 =>
            -- One of the premise coincides with the conclusion.
            exact h7
          case inr h14 =>
            -- One of the premise coincides with the conclusion.
            exact h7
        case inr h15 =>
          -- False on the left can always be used.
          apply False.elim h15
      case inr h16 =>
        -- One of the premise coincides with the conclusion.
        exact h7
  case inr h17 =>
    -- One of the premise coincides with the conclusion.
    exact h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_647565929804528920050938511936 : ((((p5 → (((p4 ∨ (((p5 ∨ False) → p4) ∨ p3)) → (False ∧ ((True ∨ p3) ∧ ((False ∨ (p2 → (p5 ∧ p1))) ∧ p4)))) → True)) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199527573148345757205591139762 : ((((((False → True) ∧ p2) ∨ p5) ∧ True) → p1) → (((p3 ∨ ((p4 → p5) ∧ ((p1 → False) ∨ p1))) ∧ (p2 ∧ p4)) → ((p1 → False) → False))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h9 : p1 := by
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h10 : ((((False → True) ∧ p2) ∨ p5) ∧ True) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h11
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h7
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h12 := h1 h10
      -- One of the premise coincides with the conclusion.
      exact h12
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h13 := h3 h9
    -- False on the left can always be used.
    apply False.elim h13
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h5.left
      let h19 := h5.right
      -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
      have h20 : p1 := by
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h21 : ((((False → True) ∧ p2) ∨ p5) ∧ True) := by
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Implications on the right can always be decomposed.
          intro h22
          -- True on the right can always be proven directly.
          apply True.intro
          -- One of the premise coincides with the conclusion.
          exact h18
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h23 := h1 h21
        -- One of the premise coincides with the conclusion.
        exact h23
      -- We have shown the premise of h17, we can now drive its conclusion.
      let h24 := h17 h20
      -- False on the left can always be used.
      apply False.elim h24
    case inr h25 =>
      -- Conjunctions on the left can always be decomposed.
      let h26 := h5.left
      let h27 := h5.right
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h28 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h25
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h29 := h3 h28
      -- False on the left can always be used.
      apply False.elim h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52373677444027301848170983844 : (((((p3 ∧ (p4 ∧ True)) ∧ (p2 → (p5 ∨ p5))) ∧ (True ∧ (p3 ∨ p3))) ∧ (p4 → ((p5 ∨ ((p5 ∨ p2) → p1)) ∨ (p5 ∧ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_243767327904433038577109598716 : ((p5 → p5) ∧ ((p2 → ((((((p2 ∧ ((p4 ∧ (True → p1)) ∧ p5)) → p4) → (p5 ∨ False)) ∨ p1) ∨ (False ∧ (p2 ∧ p3))) ∨ p2)) ∨ p5)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_758484072128900844768524423241 : (((p2 ∧ ((p1 ∨ (((p4 ∧ p4) → (p2 ∨ (p4 ∧ True))) ∧ (False ∨ (((((p5 ∧ True) → (True → p3)) ∨ p5) ∨ p4) ∧ p3)))) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_715484588974549893160493745711 : ((((((p1 ∧ p4) → p2) ∧ p3) ∧ (p5 ∨ (p2 ∨ (((False ∨ (False ∧ ((p4 ∨ (p3 ∧ True)) ∧ ((True ∧ p2) → p1)))) ∧ p3) ∨ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_725928108880715664724776721228 : (((((p2 → False) ∧ p4) ∨ (((p1 ∨ p1) ∨ True) → (p2 ∨ ((p2 ∧ p1) ∨ ((((((p2 ∧ p2) ∧ True) ∧ p5) ∧ p4) → p5) → True))))) ∨ False) ∧ True) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h4
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111782535027409643357188823609 : ((((((((((p5 → p1) ∧ p1) → p4) ∧ ((p5 ∧ (True → p2)) → p5)) ∨ p1) ∧ p1) ∨ (p4 → False)) ∨ (p4 → True)) ∨ p5) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698957365961417541098105307910 : ((((p5 ∧ ((p3 ∧ ((p3 → (True ∨ p4)) ∨ (False → p3))) → p4)) ∨ (((p5 ∨ ((p5 ∨ p2) → p2)) ∧ (p4 → p5)) ∧ (True → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245916229224590653475704817048 : ((p3 ∧ p5) ∨ (((p5 ∨ p3) ∧ ((p1 ∨ p5) → True)) → (((((True ∧ True) ∨ (p1 ∨ (False → False))) → (p4 → p3)) ∨ True) → (p2 ∨ True)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
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
    -- Conjunctions on the left can always be decomposed.
    let h9 := h1.left
    let h10 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63238663943224406360120032930 : ((p5 ∧ ((((False ∧ (p2 → p2)) ∧ p1) ∨ (False ∨ (p1 → (p2 ∧ p3)))) ∨ ((p5 ∨ True) ∨ ((p5 ∧ (p4 → True)) ∧ (p3 ∨ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_787989230099428599245081022077 : (((p4 ∨ (p5 → ((p3 ∧ (False ∧ (False ∧ ((p3 ∨ False) ∨ p3)))) ∧ (False ∧ (p1 ∨ ((p4 ∨ p3) ∨ (((p5 ∨ p3) ∧ p3) → p3))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351742170577010526886469758877 : (p4 → ((p1 ∨ (((p4 ∧ ((False ∧ p1) ∧ (False ∨ False))) ∨ p3) ∨ (False → True))) ∨ (((p5 ∧ p5) → (True ∨ True)) ∨ (p2 → (p2 ∧ False))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58598937308702784092581011789 : (((False → False) ∧ ((p2 ∨ (False ∨ (p2 ∨ ((p3 → False) → ((p1 → p5) → p5))))) ∨ (p4 ∨ (p2 ∧ (p2 → (False ∧ (p1 ∨ p1))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60415010774419279960526314798 : (((p4 → p1) → ((False ∨ (False ∨ (((p2 ∧ p5) ∨ ((p1 ∨ p2) ∨ False)) ∨ (False ∨ p4)))) ∧ (((True → p1) → p2) → (p3 ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705707700889973611413089258214 : (((((((p4 → p5) → True) ∧ False) ∨ (p5 ∨ p2)) ∧ (((p3 → (p2 ∧ True)) ∧ (((p1 ∨ p4) ∨ True) ∨ (p2 → (True → False)))) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48621859992056248237477913531 : (((((p3 → (p2 ∧ ((p2 → ((True ∨ True) ∧ ((p5 ∧ p5) ∧ p1))) → p1))) ∧ p4) ∧ ((p3 ∧ p1) ∧ False)) ∧ ((False ∧ p2) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166734852332847268330990906301 : ((p4 → (((False ∨ (False ∧ (((p1 → False) ∨ p4) ∨ p4))) ∧ ((p1 ∨ False) ∧ p3)) ∨ p4)) ∨ ((((p3 ∨ True) ∧ p3) ∨ False) ∧ (p4 → True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305769155043817316825083073882 : (p1 ∨ ((((False ∨ (p3 ∧ False)) ∧ False) ∨ (True ∧ True)) ∨ ((((p1 ∧ (p3 ∨ p1)) ∨ (False ∧ (True ∨ False))) ∨ True) → (p2 ∨ (p1 ∧ p1))))) := by
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
theorem thm_5_vars_160444516533721890321102577432 : (((((((p3 ∨ p4) → (False → (p5 ∧ p1))) → (False ∨ p1)) ∧ p1) ∨ True) → ((p1 → p2) ∧ False)) → (p2 ∧ (True → ((True ∨ False) → False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((p3 ∨ p4) → (False → (p5 ∧ p1))) → (False ∨ p1)) ∧ p1) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h8 : (((((p3 ∨ p4) → (False → (p5 ∧ p1))) → (False ∨ p1)) ∧ p1) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h9 := h1 h8
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186749647853243966057688325447 : ((((p4 ∧ (True ∨ (p1 ∧ True))) → p4) → (p4 ∧ (True → True))) → (((p3 ∧ p3) ∨ ((False ∨ p2) ∨ False)) ∨ ((p3 ∨ (p4 ∨ False)) ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p4 ∧ (True ∨ (p1 ∧ True))) → p4) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- One of the premise coincides with the conclusion.
      exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h2
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h11
  -- One of the premise coincides with the conclusion.
  exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247314309500670271245809913235 : ((False ∨ False) ∨ ((p2 ∧ ((p3 ∧ p4) ∨ True)) ∨ (True ∧ (p2 ∨ (p5 → (p2 ∨ ((p3 ∧ ((((p2 → p4) ∨ False) ∧ True) ∨ True)) → p3))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h9
  case inr h10 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231881374528996294351629264479 : (((True ∨ p2) → p5) → (p4 ∨ ((True ∧ ((p1 → ((p2 → ((True ∧ (p3 ∨ (True ∨ p1))) ∧ p3)) ∧ p1)) → ((True → p2) ∧ p1))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_750741010102703692656263961015 : (((True ∧ (((p2 ∧ False) → ((((False ∧ p5) ∨ (p5 → p2)) ∨ p3) ∨ (p4 ∧ p4))) → (False ∨ (p5 ∧ ((p2 ∧ (p3 ∧ p4)) → p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40159252064248854536134703944 : (((((((p4 → p2) → (p4 ∨ (False ∧ p2))) → (p5 ∨ p3)) ∨ (((((False → p4) ∧ False) → p5) → p5) → (True ∧ False))) ∧ p2) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_766880026714604972565178027042 : (((p4 ∧ (p5 ∨ ((((p5 → False) ∧ ((False ∧ p4) ∨ p4)) ∨ (True ∧ (p2 → ((p5 → True) → p5)))) → ((p4 ∧ p5) ∧ (True ∨ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307729911537903953958191473341 : (p1 ∨ (p3 → ((p3 ∧ (((True ∧ (p5 ∨ ((p3 → p1) ∨ p5))) ∨ ((p4 ∨ p3) ∧ (p3 ∧ (False → p4)))) ∧ (True ∨ (p3 ∨ p1)))) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_239178468924007009759083825077 : ((p2 ∨ True) ∧ (((p5 ∧ p4) ∨ p1) ∨ ((p4 ∧ (p1 ∨ (p3 ∨ p2))) ∨ ((True → ((((p5 → p3) → p3) → p3) → True)) ∨ (p1 ∧ p1))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325930459533902867391417320231 : (p5 ∨ (p5 ∨ (((((((True ∧ (False ∧ False)) → p3) ∨ p1) → p3) ∨ p3) ∨ (((p1 → p4) ∨ p4) ∨ (p3 → True))) ∧ ((p1 ∨ False) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66819758373623575661159730405 : ((True → (True → (((((p1 → ((p5 ∨ p3) ∧ False)) ∨ (True → (True → p3))) → False) ∨ True) ∨ ((p1 ∨ ((p5 → p2) ∨ False)) ∧ p3)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_790653351546502531063627932008 : (((p5 ∨ (p4 ∨ (((p5 → False) ∨ False) ∧ (((p4 → p4) ∧ (True ∧ (((False ∨ p3) ∧ ((p1 ∧ p3) → False)) ∧ p5))) → (False ∧ p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134569380731398162991501011020 : (((((((p5 ∧ ((((False ∨ p1) → p3) ∨ p4) → True)) → (p1 ∧ p1)) ∨ (p3 ∨ True)) → p4) ∧ (False → p5)) → p3) ∨ (True ∨ (True → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117216219441907566694577831682 : ((True ∧ (((p5 ∨ p3) → p5) ∨ (((True → ((True ∨ p4) ∨ (p3 → (p5 ∨ p2)))) → (p5 → False)) ∨ (True ∧ (True ∨ p1))))) ∨ (p5 ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41771545893069543095381555044 : ((((p3 ∨ ((p4 ∨ p3) ∧ False)) ∨ (((((p4 ∧ p1) ∧ (p3 → ((p5 → (p2 ∨ (p3 ∨ p3))) → p4))) → p2) ∨ False) ∨ True)) ∨ p4) ∨ p3) := by
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
theorem thm_5_vars_67388399719508582908481919233 : ((p1 → (((p5 ∨ p1) → ((p2 ∧ (((p5 ∨ p2) ∨ (False ∨ False)) ∨ p1)) ∧ ((((True → p2) → p4) → (p2 → p2)) ∧ False))) → p5)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p5 ∨ p1) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258184933832330516292118825927 : ((p4 ∨ p4) → ((p3 ∧ ((p4 ∨ True) ∧ p1)) ∨ (((p5 → p5) ∧ p3) ∨ (((False → (p5 → p1)) → (p4 ∨ p4)) ∧ (False → (p5 ∨ p1)))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149977190474249427966436283218 : ((p4 ∨ ((((p3 ∧ (p1 → False)) ∧ p4) ∨ p3) → ((((p1 ∧ (True ∧ p4)) → (p5 ∧ p1)) → p5) ∧ p2))) ∨ (False → (p3 ∨ (p1 → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699169148403749124431059619295 : ((((p1 → (((p4 ∨ p4) ∨ (p3 ∧ (p1 ∨ p2))) ∨ (p2 ∨ False))) ∨ (p2 ∧ ((True → ((p2 → (p1 ∧ p4)) ∧ (p3 → p2))) ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159883658177610576264883606086 : ((((p3 ∨ (((False ∨ p3) → ((((False → p5) ∧ (p4 → False)) → True) → p1)) ∧ p4)) ∧ p2) → p5) → (((p1 ∨ p4) ∧ False) ∨ (p5 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178393443059575340134622074622 : (((((p1 → (p3 ∨ p2)) ∧ p3) ∨ ((True → False) ∧ p1)) → (p4 ∨ False)) ∨ (((p2 ∧ (p1 ∨ p5)) ∧ (p1 → p4)) → (p1 → (p1 ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Conjunctions on the left can always be decomposed.
  let h9 := h1.left
  let h10 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h9.left
  let h12 := h9.right
  -- Disjunctions on the left can always be decomposed.
  cases h12
  case inl h13 =>
    -- One of the premise coincides with the conclusion.
    exact h13
  case inr h14 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135056698661525955750092020647 : (((((False → ((((p5 → p1) → p1) → p5) → ((p4 ∨ ((False ∨ True) ∧ p4)) ∨ False))) ∨ p2) → p2) ∨ (p3 ∨ True)) ∨ (False ∨ (p2 → p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_298902565361265870579494427886 : (False ∨ (((((p3 → p5) ∨ p1) ∧ p1) ∨ ((p5 ∧ ((False ∨ ((p1 ∧ ((p3 ∨ p3) → p2)) ∨ (p2 → p2))) ∨ False)) ∨ (p4 ∨ True))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226927389860043536427215347466 : (((True ∨ p3) → p5) ∨ (p2 ∨ ((p1 ∧ (p2 ∨ (p4 → p3))) → ((p5 ∧ (True ∧ (p5 → (True → (p5 → p2))))) ∨ (p2 ∨ (p3 → p3)))))) := by
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
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166039774481562796011612426151 : (((p3 → p4) ∨ ((p1 ∧ ((False ∧ (p4 → p5)) ∨ True)) ∨ ((p4 ∧ (p1 ∨ p4)) → False))) ∨ ((p3 ∧ (p5 ∧ (p3 ∨ p1))) ∨ (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198701298863494589034427480359 : ((p5 ∨ ((((True → p2) ∧ p1) ∨ p3) ∧ p1)) ∨ ((p5 → (p2 → (True → ((True ∨ p2) ∨ ((True ∨ (p1 ∨ p5)) ∨ p2))))) → (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171964011257781511716501913653 : ((((True ∧ p4) → (False ∧ ((False ∧ (p4 ∨ True)) → (p1 ∧ p3)))) ∧ (p1 ∨ False)) ∨ ((((p2 ∨ p1) ∨ p2) ∨ ((p4 ∧ p2) ∨ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165064543202262770461773650364 : (((p1 ∧ (p4 ∨ (p3 ∨ (p1 ∧ (p5 ∧ (False ∨ ((p4 → p4) ∧ (p1 → True)))))))) → p4) ∨ (((p5 → p3) ∨ False) → (p2 → (p2 ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259188205195729111248793089051 : ((False → False) → ((((p2 → True) ∧ ((((False ∨ ((p5 → (p4 ∨ True)) ∧ p3)) ∧ False) ∧ (False ∧ True)) ∨ (p2 → (p3 → False)))) ∨ True) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115517044678200902434724360490 : (((((p2 ∧ p3) ∨ p2) → (False ∧ (False → p2))) → (((p3 ∨ (True ∧ (p1 → (p5 ∧ p4)))) ∨ True) ∨ ((p4 ∧ True) ∨ p1))) ∨ (p2 ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317849856878854044365870560437 : (p4 ∨ (((p3 ∧ p5) ∧ ((False ∧ (p1 ∧ True)) ∨ ((p5 ∨ p3) ∨ ((p1 ∨ False) → ((p2 ∨ ((p2 ∧ p3) ∨ (p4 ∨ p2))) → p4))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_874530480680062272521223805386 : (((((((p1 → p4) ∧ (((p1 → (p2 ∧ p4)) → True) ∨ (p4 ∧ (p5 ∧ p2)))) ∧ (((p1 → p2) → p1) ∧ p2)) ∧ p4) ∧ (p3 → p5)) → p1) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h7.left
    let h12 := h7.right
    -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
    have h13 : (p1 → p2) := by
      -- Implications on the right can always be decomposed.
      intro h14
      -- One of the premise coincides with the conclusion.
      exact h12
    -- We have shown the premise of h11, we can now drive its conclusion.
    let h15 := h11 h13
    -- One of the premise coincides with the conclusion.
    exact h15
  case inr h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- Conjunctions on the left can always be decomposed.
    let h21 := h7.left
    let h22 := h7.right
    -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
    have h23 : (p1 → p2) := by
      -- Implications on the right can always be decomposed.
      intro h24
      -- One of the premise coincides with the conclusion.
      exact h22
    -- We have shown the premise of h21, we can now drive its conclusion.
    let h25 := h21 h23
    -- One of the premise coincides with the conclusion.
    exact h25
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_462654463524902623057580847931 : ((((((False → (p2 → (p2 ∧ ((p5 → p1) ∧ p2)))) ∧ ((p1 ∨ p1) → p2)) → p5) ∨ ((p3 → p1) ∨ ((p4 ∨ True) ∨ (p5 ∨ p1)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205954743994431900553874715451 : ((False ∧ (p5 ∨ (p2 → (p2 ∨ p5)))) ∨ ((((False ∨ (p5 ∨ ((p2 ∨ p5) ∨ p1))) → ((p1 ∧ p3) → p5)) → (p4 ∨ (True ∧ p5))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38711220982791554000570023845 : ((((True → ((p3 ∨ (p2 ∨ p4)) ∨ p1)) ∨ (((True ∧ p1) ∧ (p2 → p5)) → (((p4 ∨ ((p4 ∨ p2) ∧ p4)) ∨ p3) ∧ p1))) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_479875958160390022281211193487 : ((((p1 ∨ (((p2 ∧ p4) ∨ (p2 ∧ p3)) → True)) ∧ (p2 ∨ ((((p3 → p4) → (p1 ∧ ((p2 → (p1 ∧ p5)) ∧ p5))) ∨ p2) ∨ True))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_57031875238390293821689173029 : (((p2 → (p1 ∧ p5)) ∧ (p3 ∧ (((p3 ∨ ((False ∧ (True → p3)) ∧ p3)) ∧ (True ∧ ((((p4 ∧ p2) ∨ p4) → p5) ∧ True))) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_634222071437040987084986499614 : (((((p2 ∧ (((False ∧ (p4 ∨ (p4 → p4))) ∧ (p3 ∧ (False ∧ ((p4 ∨ p3) → (False → (p5 → p2)))))) ∨ p1)) → (True ∨ p4)) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175087572905150342539142562068 : ((p3 ∧ ((p1 → p3) → (((p3 ∧ (p4 ∨ p5)) → ((p1 → True) ∨ p1)) ∧ False))) → ((p2 ∨ p1) → (True → (((p3 → p2) → p2) → False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h1.left
    let h7 := h1.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : (p1 → p3) := by
      -- Implications on the right can always be decomposed.
      intro h9
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h10 := h7 h8
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h1.left
    let h14 := h1.right
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h15 : (p1 → p3) := by
      -- Implications on the right can always be decomposed.
      intro h16
      -- One of the premise coincides with the conclusion.
      exact h13
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h17 := h14 h15
    -- We need to get the right conjuct of h17 based on <expert-advice>.
    let h18 := h17.right
    -- False on the left can always be used.
    apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208440585177679181740051351685 : (((True → True) ∨ ((p2 ∨ p1) ∨ p4)) → ((p5 ∨ (((False → (p5 ∧ (p5 ∨ p2))) → (p3 ∨ True)) ∨ ((False ∨ True) → (p3 ∨ p1)))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
        -- Implications on the right can always be decomposed.
        intro h7
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h9
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h11
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214507738695515325894979762861 : (((p3 ∧ p3) ∧ (p5 ∨ p4)) ∨ ((p2 ∨ ((p5 → (((p2 → p2) ∨ p5) ∨ (p1 → (p4 → p4)))) ∨ (p5 ∨ p2))) ∧ ((True ∧ True) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52215626173670576010812675956 : ((((p5 → p1) ∨ ((True ∨ (p1 ∨ (p2 → (False ∧ p5)))) ∧ (p4 ∨ (False → p5)))) → ((((False → False) → (p4 ∧ p5)) ∨ p3) ∨ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
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
      cases h9
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_605081329758401223945077981897 : ((((p2 → (((p5 ∨ p1) ∧ ((((((False → p3) → (p4 ∧ (p1 ∧ ((p2 ∨ p4) ∧ p3)))) ∧ p3) ∨ False) ∨ p3) → False)) → False)) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350459196055200353262869738364 : (p4 → ((((p3 ∨ (((p3 → p5) ∨ p1) ∨ (p1 ∧ True))) ∨ ((p5 ∧ (((p4 → p3) ∨ p5) → (False ∨ (p4 ∧ p1)))) → p1)) → p3) → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((p3 ∨ (((p3 → p5) ∨ p1) ∨ (p1 ∧ True))) ∨ ((p5 ∧ (((p4 → p3) ∨ p5) → (False ∨ (p4 ∧ p1)))) → p1)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : ((p4 → p3) ∨ p5) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h8 := h6 h7
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- One of the premise coincides with the conclusion.
      exact h12
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h13 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180634060807690694230309432611 : ((((((False → p1) ∨ False) ∨ p2) ∨ p2) ∨ ((p2 → (p5 ∧ p5)) ∨ p4)) → ((True ∧ (p1 → p5)) ∨ ((False → (p1 ∨ (True → True))) ∨ True))) := by
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
          -- False on the left can always be used.
          apply False.elim h6
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
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147708921571340320768452311191 : (((((p4 → p4) ∨ ((False → (p4 → p4)) ∨ (p3 ∨ p2))) ∨ (p1 → (False ∧ (p4 ∧ (p4 → p2))))) → p2) ∨ (((p3 ∧ p4) ∨ p2) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150322005085626388483302607093 : ((p4 → (True → (p2 → ((((p3 ∧ (p3 ∨ ((p2 ∨ p3) ∨ p3))) ∨ (True ∧ (False ∧ p1))) ∧ p5) ∨ p4)))) ∨ ((False → (p1 → p2)) ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3001061551599400640165577458 : (((p1 ∧ False) ∨ p2) → ((((True → (False ∨ (p5 ∧ False))) ∧ ((p2 → p4) → ((p4 ∧ p5) ∧ ((p4 → p3) → p4)))) ∨ p2) ∧ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52373753552037792138355863891 : ((((((p1 ∧ False) ∨ p1) ∨ ((p5 → p4) ∧ p2)) ∧ (False ∧ (True ∨ p1))) ∧ (p4 ∨ ((p5 ∨ (((p4 ∧ p5) ∨ p1) ∨ p2)) ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216487708059990031057356448814 : ((p5 → ((p5 ∧ p3) ∨ False)) ∨ ((p4 → (p2 → (p2 ∧ (p5 → ((((p1 → p4) → ((p2 ∧ p3) ∧ True)) ∨ p3) ∧ p4))))) ∨ (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184348186863227095967966389992 : (((p4 ∧ ((False ∨ (p1 → (p2 ∧ p5))) ∧ (p5 ∨ p1))) → False) ∨ (True ∨ ((False → (p2 ∧ p1)) → ((p1 ∨ p1) → (False ∧ (p3 → p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158476159234579866184409292431 : (((p5 → p2) ∨ ((p3 ∨ (p3 ∧ ((p3 ∨ (True → p1)) ∨ (True ∧ False)))) ∨ ((p4 ∨ p4) ∧ p4))) ∨ (p2 ∨ (True ∨ ((p3 ∨ False) ∧ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225200549659706261672508859506 : (((p4 ∧ p4) ∧ p5) ∨ ((p5 → (((((p2 ∨ ((p3 ∨ p2) ∧ p3)) → p5) → ((p1 → p5) ∧ False)) ∨ ((p1 ∨ p1) → True)) ∨ p3)) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_83251080308178625265788251961 : (((((p2 ∧ p1) ∨ (True ∨ (p3 → ((p5 ∨ (((p3 ∧ p5) ∧ False) ∧ True)) → p2)))) → p5) ∧ (p5 → ((False → (p2 ∨ p2)) → p3))) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p2 ∧ p1) ∨ (True ∨ (p3 → ((p5 ∨ (((p3 ∧ p5) ∧ False) ∧ True)) → p2)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h6 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h6
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : (False → (p2 ∨ p2)) := by
    -- Implications on the right can always be decomposed.
    intro h9
    -- False on the left can always be used.
    apply False.elim h9
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h10 := h7 h8
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158022593172550742628826321254 : ((((False ∨ p2) ∨ ((p5 ∧ p1) ∧ p3)) ∧ (False → (p4 → ((p4 ∨ p2) ∨ (p3 → (p5 ∧ p1)))))) ∨ (False → (True ∨ (p4 ∨ (p1 → p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670576431866857821728027363374 : (((((p4 ∨ p2) ∨ (((((p1 ∧ False) → p5) ∧ p2) ∧ (p5 ∨ (p4 ∧ (p4 ∧ (p2 ∨ (True → p5)))))) ∨ p3)) ∨ ((True ∧ p4) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193155951475982796826175504733 : (((p4 ∨ ((p3 ∨ False) ∨ False)) ∨ (False → (p3 ∨ p3))) → ((((False ∨ ((p4 → ((p2 ∧ True) → p2)) → p3)) ∧ p1) ∧ p2) ∨ (False → p4))) := by
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
      -- Implications on the right can always be decomposed.
      intro h4
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h8
          -- False on the left can always be used.
          apply False.elim h8
        case inr h9 =>
          -- False on the left can always be used.
          apply False.elim h9
      case inr h10 =>
        -- False on the left can always be used.
        apply False.elim h10
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_600176972127796190966586495986 : (((((False → True) → (((p4 → p1) ∨ p1) ∨ ((((p3 ∨ p1) ∧ ((p4 → False) ∧ (((p5 ∨ p4) → p1) ∧ p2))) ∧ False) ∨ p3))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310888432233723591531334356238 : (p2 ∨ ((p1 → (p1 ∨ p4)) → (True ∧ (p1 ∨ (((p4 ∨ p4) ∨ p3) ∨ ((((p3 ∧ (False ∧ p5)) → p3) ∨ True) ∨ ((p4 ∨ p3) ∨ p1))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_316878802895609859474389817965 : (p3 ∨ (p1 → ((((p3 ∨ p2) ∧ p3) ∨ (p1 ∨ True)) → (((True ∧ False) → (True ∧ p2)) ∧ ((p4 → (False ∧ ((p1 ∧ False) → p1))) ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h5
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358104959716490074868100466739 : (p5 → (p2 ∨ ((((((p3 ∧ p3) ∨ ((((p4 → p1) ∨ (p3 ∨ (p3 ∧ p2))) → False) → p3)) ∨ p2) → p4) ∨ (True ∨ p2)) ∧ (p1 → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117182488316542754670808708662 : ((True ∧ ((p3 → ((p2 ∧ ((True ∧ p2) ∧ (((p2 → p5) ∧ False) ∨ ((p3 ∨ p5) ∨ (p4 ∧ False))))) ∨ p2)) ∨ (p3 → True))) ∨ (p4 → False)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114176231998915728047093215878 : (((((((True ∧ p4) ∧ ((((p4 → p2) → p3) ∧ (p3 ∨ p5)) → p2)) ∧ p5) ∧ True) → (p2 ∧ False)) → (p1 → (p1 ∧ p4))) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328790820047044374303529909363 : (True → ((((True ∨ (p4 → False)) → (p2 ∨ p5)) ∨ (p1 ∧ p5)) ∨ ((True ∨ (((p4 ∨ True) ∨ p4) ∧ (p5 → (False ∨ p5)))) → (p1 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_642713562860928003773215000666 : ((((p1 ∧ (((True → p2) ∧ p2) → (p2 ∨ ((((p5 ∧ (True ∨ (True → (p4 ∧ (p2 ∧ p5))))) ∧ (p5 → False)) ∨ p4) ∧ p5)))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264085800211272571728985859014 : (True ∧ ((p3 → (((False → (p4 ∧ p4)) ∨ (False ∧ p1)) → False)) ∨ (((((p2 ∨ (p5 → p2)) ∨ (True ∧ (p1 ∧ False))) ∨ True) → p2) ∨ True))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111560155888065489683812069339 : (((((p2 ∧ (p1 ∨ ((((True ∨ p5) ∧ p2) ∧ p4) ∨ True))) ∨ (((p3 ∨ False) ∨ (p3 ∧ p3)) ∨ (p4 ∨ p3))) ∧ p2) ∨ p5) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137430221527371105043040728055 : ((p4 ∧ (((((((p2 ∨ ((p3 ∧ p1) ∨ p1)) ∨ p3) ∨ True) ∧ ((p5 ∧ True) ∧ p2)) ∨ p5) ∧ True) ∧ (p1 → p5))) ∨ ((p5 ∨ p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_737453614451955240920653936160 : ((((p4 → p5) ∧ ((p5 ∧ ((((p4 ∨ ((True ∧ p1) → p2)) → p2) ∧ p5) ∧ (p4 → p1))) ∧ ((((p4 ∧ False) ∧ p3) ∧ p1) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624737534086921281969347045795 : ((((p4 ∨ (p4 → (p5 → (((p3 ∧ (p1 ∧ (p1 ∧ p3))) → (False ∧ ((False ∧ True) → p5))) ∧ (p3 → ((p2 → True) → False)))))) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185391567858856959165244564203 : ((p5 ∧ (p4 ∨ ((p5 ∧ ((p1 ∨ p4) → (p2 ∧ p2))) ∨ p3))) ∨ ((((p1 ∧ (True → True)) ∧ p1) → p2) ∨ ((False ∨ (False ∨ True)) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_730124189569215003815881787102 : (((((p4 ∨ p1) → p5) → (False ∨ (((p4 ∨ p2) ∧ p1) ∨ (p2 → (p4 ∨ (True ∨ ((False ∧ p5) ∧ (((p2 ∨ True) ∨ False) ∧ True)))))))) ∨ p1) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225142140440104581585129154981 : (((p3 ∧ p1) ∧ p2) ∨ ((((p1 ∨ (p1 ∧ p1)) → ((False ∧ p3) ∨ (p5 → True))) → p4) ∨ ((True ∧ (p3 ∧ (False → p5))) → (p3 ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339674755306649265027689899263 : (p1 → (p3 ∨ ((((p5 → (p1 → ((p2 ∨ (((True ∨ True) ∨ ((p4 → (False → p3)) ∨ p1)) ∨ p5)) → p4))) ∨ p4) ∨ p1) ∨ (p5 ∨ p3)))) := by
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
theorem thm_5_vars_252945758723265616231572881458 : ((True ∧ p2) → (((((((False → (p2 ∧ p3)) → p3) ∧ p1) ∧ p2) ∨ p1) ∨ (p4 → (((p1 ∧ p5) ∨ (True ∨ p5)) ∨ p3))) ∨ (p4 ∨ p2))) := by
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
theorem thm_5_vars_40161531291175996254982153928 : ((((((p2 ∨ ((p2 ∨ p4) ∨ p3)) ∨ (p1 ∧ (p5 → False))) → ((((p1 → p3) ∧ p4) → ((p4 ∨ False) ∧ False)) → p3)) ∧ False) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669417413856733669628232631606 : ((((((((p2 → (p4 ∨ (p3 ∨ p2))) ∧ True) → (p5 → p3)) → ((p4 ∨ (p3 ∧ p4)) ∧ False)) ∨ (p2 ∧ p1)) ∨ ((False → True) ∨ p3)) ∨ p1) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257625684361728076800032872905 : ((p3 ∨ p2) → (((((p5 ∧ False) → p5) ∧ (True ∨ p5)) ∧ (((p2 ∧ (True ∧ (False ∨ False))) ∧ (True → p3)) ∧ p1)) ∨ ((False ∨ False) → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- False on the left can always be used.
      apply False.elim h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h9



