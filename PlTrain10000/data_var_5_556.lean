variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157205082055374759825006792228 : ((((p3 → ((p2 ∧ p4) → (((p4 ∧ (p2 → False)) ∨ p1) ∧ (p5 → True)))) ∨ (False ∨ p5)) → p2) ∨ (((p5 ∧ True) ∧ False) ∨ (p2 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693123204169236319303901473082 : ((((p4 ∧ (((p4 ∧ ((p5 ∧ p5) → ((True ∧ p3) ∧ p3))) ∧ p1) ∧ p3)) ∧ ((p2 ∨ (((p2 ∨ p2) ∨ p1) ∨ p1)) ∨ (p1 ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40089563767107971604227263335 : ((((((p1 ∧ p2) ∧ ((p4 ∧ (p4 ∧ ((p4 ∨ p2) → p2))) ∧ (p1 ∧ ((((p5 ∨ p3) ∧ p5) ∨ True) ∧ p3)))) → False) ∧ p1) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_82911083364370701936095035265 : ((((False ∧ ((p1 → p5) ∨ ((p1 ∧ p4) ∨ (((False ∨ False) ∧ ((p3 → False) ∧ False)) ∨ True)))) ∨ True) → ((p3 ∧ (p2 → p4)) ∧ p4)) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False ∧ ((p1 → p5) ∨ ((p1 ∧ p4) ∨ (((False ∨ False) ∧ ((p3 → False) ∧ False)) ∨ True)))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348178691075316225928369846368 : (p3 → ((p3 ∨ True) → (p5 ∨ ((p2 ∧ (p3 → ((p4 → ((True ∧ (False ∧ ((p5 ∧ p2) ∧ p2))) ∨ ((p1 ∧ p4) ∨ p3))) → p4))) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_717136110147547907057489892406 : ((((False ∨ (False → (p3 ∧ False))) ∧ (p3 ∨ (((p3 → (True ∨ (p4 ∧ ((p2 → p3) ∧ p5)))) → (p5 ∧ (p3 ∧ (True → p3)))) ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180986156739266979406997887652 : (((p1 ∧ True) ∨ (False → ((p3 → p1) ∨ ((False → (p5 → p4)) ∨ True)))) → ((p5 ∨ (((p1 ∨ (p2 ∨ (False ∧ True))) ∨ True) ∨ p4)) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356200284330167488822054634715 : (p5 → (((True ∨ p4) ∨ (p5 ∨ (True → ((p1 ∧ p5) → (((p4 ∧ p5) ∨ p3) ∨ (p3 ∧ p3)))))) → (p1 → ((p4 ∧ (p1 → p3)) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116314592015217650683672567502 : (((p4 → (p2 → p5)) ∨ (p5 ∨ ((((((False → False) ∧ p4) ∨ ((((False ∧ True) ∧ p2) → p5) ∧ p3)) ∧ p3) → False) ∨ True))) ∨ (p2 ∨ p5)) := by
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
theorem thm_5_vars_50354252677047986366072326171 : ((((p5 ∧ ((p3 → p3) ∧ p5)) ∨ ((True ∨ ((p2 ∨ p3) ∧ (p2 → ((p3 ∨ False) → p1)))) → False)) ∨ (False → ((p1 ∧ p2) ∧ True))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114693011810650454996446041748 : (((p4 → (p2 ∨ ((p4 ∨ (True ∨ (((p4 ∨ False) ∧ (p4 ∨ p1)) → p1))) ∧ p2))) ∨ (((p2 → p1) ∧ p2) ∨ (False → p3))) ∨ (p2 ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_212189599518161791890365155976 : ((True ∨ (p1 ∨ (p5 ∧ p5))) ∧ ((((p1 → ((p4 ∨ (p4 ∧ p2)) → False)) ∨ (False → (p2 ∧ ((p5 → p4) → p1)))) → False) → (False ∧ p2))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p1 → ((p4 ∨ (p4 ∧ p2)) → False)) ∨ (False → (p2 ∧ ((p5 → p4) → p1)))) := by
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- False on the left can always be used.
  apply False.elim h5
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : ((p1 → ((p4 ∨ (p4 ∧ p2)) → False)) ∨ (False → (p2 ∧ ((p5 → p4) → p1)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h6
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727342588799216306761680323824 : ((((p2 ∧ (False ∧ p4)) ∨ (p3 ∧ ((False ∨ ((((((p4 ∨ p4) ∧ p1) ∧ p1) ∨ p5) ∧ (p5 ∨ (p5 ∨ True))) ∧ (p3 ∨ True))) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309311068402976348114456220290 : (p2 ∨ ((((((p1 ∨ ((p4 ∨ p2) ∧ ((p2 → False) ∧ p2))) ∨ (p2 ∧ p2)) ∨ True) ∧ (p1 ∧ ((p1 ∨ p1) ∨ False))) ∨ True) ∨ (True ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326879709950517912987391331874 : (True → (((((False ∨ (False → p4)) → (p1 ∨ (p1 ∧ p4))) → (((True → (((p1 ∨ True) ∨ p4) → p5)) ∨ (p3 ∨ p1)) ∨ p4)) ∨ True) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317723998251910647686768425233 : (p4 ∨ (((p2 → (p1 → (((p4 ∧ ((p1 ∧ False) ∧ False)) → (((True ∨ True) ∧ (False ∧ (p2 ∨ False))) ∧ p5)) → True))) → (p3 ∨ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53210586535858660337322288773 : ((((p5 ∧ (((p5 ∨ False) ∨ p1) ∨ p4)) ∧ ((False ∨ p2) ∨ p3)) ∨ (p4 ∨ ((((p1 ∨ (p1 → p1)) ∧ p3) → True) ∨ (p4 ∨ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_902752596074009174392316524085 : (((((p2 → (True ∧ p5)) ∧ ((False ∨ ((p5 → False) ∧ (((p5 ∧ p5) → (p4 ∨ False)) ∧ True))) ∧ p2)) ∧ ((p3 ∧ p2) → (p5 → p5))) → p1) ∧ True) := by
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
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h14 : p5 := by
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h15 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h16 := h4 h15
      -- We need to get the right conjuct of h16 based on <expert-advice>.
      let h17 := h16.right
      -- One of the premise coincides with the conclusion.
      exact h17
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h18 := h10 h14
    -- False on the left can always be used.
    apply False.elim h18
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_605127337537644968051152860685 : ((((p2 → ((p2 → ((p1 ∨ ((p2 ∨ p2) → (((True ∧ p2) ∧ p5) ∨ (p1 ∨ p5)))) ∧ p3)) ∧ (p5 → ((p3 ∧ p4) ∧ p5)))) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204163188199962346256977846365 : (((((p2 ∨ True) → p2) ∨ p3) ∧ p4) ∨ (((False ∨ p3) ∨ (p5 → ((p3 ∧ (True ∨ (True ∨ (False ∨ p2)))) ∨ ((p2 → p5) → p2)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_155036984254588618998168244997 : ((((p3 → ((True → True) ∨ ((True ∧ p5) ∨ p3))) → (p4 → p3)) ∨ (False → ((False ∨ p1) ∨ p3))) ∧ (((p2 ∨ p3) ∧ (p5 ∧ False)) → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51555195496817475219941121039 : (((p5 ∧ (((((p1 → (p4 ∧ p3)) ∧ p5) ∨ p1) ∨ p4) ∧ ((p2 ∨ (p3 → p3)) ∨ False))) → (p2 → ((p3 ∨ p5) ∧ (p1 → True)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h10
        case inr h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h10
      case inr h14 =>
        -- False on the left can always be used.
        apply False.elim h14
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h17 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h18 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h3
      case inr h19 =>
        -- False on the left can always be used.
        apply False.elim h19
  case inr h20 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h21 =>
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h22 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h23 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
    case inr h24 =>
      -- False on the left can always be used.
      apply False.elim h24
  -- Implications on the right can always be decomposed.
  intro h25
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62878069755466259816954322163 : ((p4 ∧ ((p3 ∨ (p1 ∨ p2)) → ((p3 ∧ (((p2 ∨ False) ∧ True) ∧ (((p1 ∨ p2) → p1) → ((False → (True ∧ True)) ∧ False)))) → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49273217123260290685619878350 : (((p3 ∧ (((p1 ∧ (False → p2)) ∧ ((False ∧ (((p4 ∧ (True ∧ p1)) ∨ p3) ∨ (False → p2))) ∧ False)) ∧ True)) ∨ (p3 ∨ (False ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136674438002567875581916903009 : (((p5 ∨ (p2 ∧ True)) → (((p5 ∨ p2) ∧ (p4 ∨ False)) ∨ (p3 ∨ ((p3 → p3) ∧ (p5 ∨ (True ∨ (p2 ∨ False))))))) ∨ (p2 ∨ (False ∧ p4))) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166325594206596505078154629614 : ((p5 ∧ ((p1 ∧ ((p3 ∧ p3) → p1)) ∧ ((p5 ∧ p4) ∧ (p4 ∨ ((p4 ∨ p1) ∧ p1))))) ∨ ((True ∧ p2) ∨ ((p2 → (p1 → False)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60497915062325041149577553888 : ((True ∧ (((((((True ∧ (p2 ∨ False)) ∧ True) ∨ False) ∨ (p3 → (p4 ∧ False))) ∧ p5) → (False ∧ (False ∧ ((False ∧ p3) → p2)))) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785919423951739551561135131272 : (((p4 ∨ ((p3 ∧ (False ∨ (p5 ∨ ((((p2 → ((((p4 ∧ (p2 ∨ p5)) ∧ p1) → False) ∧ p5)) ∧ False) ∨ True) → p1)))) ∧ (p4 ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67794339307569316763042625644 : ((p2 → ((((p2 → (p3 ∨ (((p3 ∨ False) → ((p5 ∧ (True ∨ (p3 ∨ p1))) ∧ p3)) → p4))) ∨ ((p2 ∧ p4) → True)) → False) → p3)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((p2 → (p3 ∨ (((p3 ∨ False) → ((p5 ∧ (True ∨ (p3 ∨ p1))) ∧ p3)) → p4))) ∨ ((p2 ∧ p4) → True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656799051526533858039049911742 : ((((((True ∨ p3) → (p2 ∨ (p5 → p2))) → ((p1 ∨ p3) → (p4 ∧ (((True → p4) → ((False → p5) ∨ True)) ∨ p4)))) ∨ (False ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45699776582423998822640403866 : (((True → (((p4 → (p1 ∨ (p1 ∧ p3))) ∨ ((True ∧ ((p3 ∨ (((True → p4) ∨ p5) ∧ p2)) → False)) → (p3 ∧ p3))) ∧ p5)) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338870466607924079673579496032 : (p1 → ((True ∧ True) → ((p2 ∨ (p2 ∧ ((p2 → p2) ∨ False))) ∨ ((p4 ∧ True) → ((False ∧ p3) ∨ (((p2 → p3) ∨ True) ∨ (True ∧ p4))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_86091418450164851822195953335 : (((p1 → (False ∧ (p4 → (p5 ∧ (p2 ∧ (p2 → p5)))))) ∧ ((p1 ∧ (p4 → (True → False))) ∧ (p3 ∨ ((False ∨ (p1 → p5)) ∨ p2)))) → p3) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h8 =>
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- False on the left can always be used.
        apply False.elim h11
      case inr h12 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h13 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h6
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h14 := h2 h13
        -- We need to get the left conjuct of h14 based on <expert-advice>.
        let h15 := h14.left
        -- False on the left can always be used.
        apply False.elim h15
    case inr h16 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h17 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h18 := h2 h17
      -- We need to get the left conjuct of h18 based on <expert-advice>.
      let h19 := h18.left
      -- False on the left can always be used.
      apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111057484330590968945612504576 : (((((((False ∧ True) ∧ (p5 → False)) ∧ ((p3 ∨ (p1 → p5)) ∨ p5)) ∧ False) ∧ (p4 ∧ (((p3 ∧ p5) ∧ p1) ∨ p3))) ∧ p5) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147738140943729256080302212261 : (((((p3 → (True → p3)) ∧ True) ∨ ((((p1 ∨ False) → False) → (p2 → ((True ∨ True) ∨ False))) ∨ p1)) → p1) ∨ (p5 ∨ ((p2 ∧ False) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_683878064420277503948984458653 : (((((False ∨ (True → (((False → (p5 ∧ p1)) → p3) ∧ (((p4 → p5) → p2) ∨ p2)))) ∨ True) ∨ ((p4 ∧ ((p5 ∨ False) ∨ p5)) ∧ p4)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_800864017383991883184398173330 : (((p2 → (((p3 → (p4 ∧ True)) → (p2 → (((True ∧ p1) → (p1 ∨ (p2 ∨ p3))) → (p1 ∨ (False ∧ (p5 → p5)))))) ∨ (False ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43481515940071274492026518877 : ((((p1 ∧ (p2 ∧ (p1 ∧ (p3 ∨ (p5 ∧ ((((p5 → False) ∨ p2) ∨ False) ∨ ((True ∧ ((False → p3) ∨ False)) ∧ True))))))) ∨ p4) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37053975352908669126927409839 : (((((((((p2 ∨ (p2 ∨ (p3 ∧ ((False ∨ p3) ∨ p4)))) ∨ p1) ∨ (p1 ∧ (p3 ∧ p3))) ∨ p3) ∨ (p2 ∨ p2)) ∧ p3) ∧ p4) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305399471367401029334958201330 : (p1 ∨ (((((p1 → ((p2 → p1) ∧ p5)) → (p2 → True)) ∨ ((p2 ∨ p1) → True)) → p3) ∨ (p4 ∨ (False ∨ (False → (p3 ∧ (False ∨ True))))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747261489471392229755439827711 : ((((p5 ∨ p2) → (((p4 ∧ p1) → False) ∨ (((p1 ∧ (p1 → p2)) ∧ ((False ∧ ((((p2 → p1) ∧ False) → True) ∨ p1)) ∧ p3)) ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_931679973828554878927892718168 : ((((((p1 → (p1 ∨ (True ∨ True))) ∨ p3) ∧ p4) ∧ ((False ∨ p2) ∧ ((False → ((p4 ∨ True) → p4)) ∧ ((p2 → (p2 ∧ False)) ∨ p1)))) → p1) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h3.left
    let h8 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h8.left
      let h12 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
        have h14 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h10
        -- We have shown the premise of h13, we can now drive its conclusion.
        let h15 := h13 h14
        -- We need to get the right conjuct of h15 based on <expert-advice>.
        let h16 := h15.right
        -- False on the left can always be used.
        apply False.elim h16
      case inr h17 =>
        -- One of the premise coincides with the conclusion.
        exact h17
  case inr h18 =>
    -- Conjunctions on the left can always be decomposed.
    let h19 := h3.left
    let h20 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h21 =>
      -- False on the left can always be used.
      apply False.elim h21
    case inr h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h20.left
      let h24 := h20.right
      -- Disjunctions on the left can always be decomposed.
      cases h24
      case inl h25 =>
        -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
        have h26 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h22
        -- We have shown the premise of h25, we can now drive its conclusion.
        let h27 := h25 h26
        -- We need to get the right conjuct of h27 based on <expert-advice>.
        let h28 := h27.right
        -- False on the left can always be used.
        apply False.elim h28
      case inr h29 =>
        -- One of the premise coincides with the conclusion.
        exact h29
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115277326320921003230608534445 : (((p4 ∨ ((p1 ∨ (p1 → (True ∨ p3))) → (p1 → p3))) ∨ ((p2 ∧ ((((p2 ∨ p4) ∨ p1) ∨ p5) ∧ (p5 ∧ False))) ∧ p4)) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256899150943373317760602999982 : ((p1 ∨ p4) → (((p3 ∨ ((p2 → True) ∨ ((True ∨ True) → (p4 ∧ (p2 ∨ False))))) → (p2 ∨ (p4 ∨ p1))) ∨ (((p1 ∧ p3) ∧ p5) ∧ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
  case inr h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h9
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305485957795282902170122422343 : (p1 ∨ ((p4 → ((p3 ∨ (p2 ∧ ((p4 ∨ (p4 ∧ False)) ∧ (p5 → p3)))) → True)) ∧ ((False ∨ p2) ∨ ((p4 ∨ p3) ∨ ((False → p2) ∨ True))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53391085022628667838523602542 : ((((p3 → (((p2 ∧ p3) → ((p2 → True) ∨ p4)) ∨ p1)) → p4) → ((p4 ∨ ((p3 ∨ False) → (((p3 → True) ∨ p4) ∧ p5))) ∨ p1)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 → (((p2 ∧ p3) → ((p2 → True) ∨ p4)) ∨ p1)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174183257231790960267009583915 : (((p4 ∨ (p5 → ((False → (False → (p5 ∨ (False ∨ True)))) ∨ p5))) ∨ (p5 → False)) → (((p1 ∧ p5) ∨ ((p2 ∧ (p5 ∧ False)) → p4)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h4
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h16
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- False on the left can always be used.
    apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_664622730543467641712308501022 : ((((True → ((((((True ∧ ((p5 → p4) ∨ (p1 → True))) → p3) → False) ∨ p4) ∨ (p1 ∧ False)) ∧ (True → (p1 → p3)))) → (p1 → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185330222405598280975444704679 : ((p3 ∧ (p1 ∨ ((((p1 → (False ∨ p5)) ∨ False) → True) → p1))) ∨ (((((True → True) ∧ (False ∨ (True ∨ p1))) ∧ (True → True)) → p3) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_644014938090507979684271925377 : ((((True ∨ (((True → p5) ∨ ((p3 ∨ (((((p1 ∧ (p5 ∨ True)) ∧ p5) ∨ p3) → (p1 ∧ p1)) ∧ True)) ∧ False)) → (p3 ∧ True))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315275250397922682465670229405 : (p3 ∨ ((((True → False) ∨ False) ∧ p3) → (((((p4 ∧ p4) ∨ p1) → (False ∧ (p1 ∧ p2))) ∧ p4) ∧ ((p4 ∨ p4) → ((p1 → p2) ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- False on the left can always be used.
      apply False.elim h11
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h1.left
    let h14 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h15 =>
      -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
      have h16 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h15, we can now drive its conclusion.
      let h17 := h15 h16
      -- False on the left can always be used.
      apply False.elim h17
    case inr h18 =>
      -- False on the left can always be used.
      apply False.elim h18
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h19.left
    let h21 := h19.right
    -- Conjunctions on the left can always be decomposed.
    let h22 := h1.left
    let h23 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h24 =>
      -- We want to use the implication h24 based on <expert-advice>. So we show its premise.
      have h25 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h24, we can now drive its conclusion.
      let h26 := h24 h25
      -- False on the left can always be used.
      apply False.elim h26
    case inr h27 =>
      -- False on the left can always be used.
      apply False.elim h27
  case inr h28 =>
    -- Conjunctions on the left can always be decomposed.
    let h29 := h1.left
    let h30 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h29
    case inl h31 =>
      -- One of the premise coincides with the conclusion.
      exact h28
    case inr h32 =>
      -- False on the left can always be used.
      apply False.elim h32
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h33 =>
    -- Conjunctions on the left can always be decomposed.
    let h34 := h33.left
    let h35 := h33.right
    -- Conjunctions on the left can always be decomposed.
    let h36 := h1.left
    let h37 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h36
    case inl h38 =>
      -- We want to use the implication h38 based on <expert-advice>. So we show its premise.
      have h39 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h38, we can now drive its conclusion.
      let h40 := h38 h39
      -- False on the left can always be used.
      apply False.elim h40
    case inr h41 =>
      -- False on the left can always be used.
      apply False.elim h41
  case inr h42 =>
    -- Conjunctions on the left can always be decomposed.
    let h43 := h1.left
    let h44 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h43
    case inl h45 =>
      -- We want to use the implication h45 based on <expert-advice>. So we show its premise.
      have h46 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h45, we can now drive its conclusion.
      let h47 := h45 h46
      -- False on the left can always be used.
      apply False.elim h47
    case inr h48 =>
      -- False on the left can always be used.
      apply False.elim h48
  -- Conjunctions on the left can always be decomposed.
  let h49 := h1.left
  let h50 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h49
  case inl h51 =>
    -- We want to use the implication h51 based on <expert-advice>. So we show its premise.
    have h52 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h51, we can now drive its conclusion.
    let h53 := h51 h52
    -- False on the left can always be used.
    apply False.elim h53
  case inr h54 =>
    -- False on the left can always be used.
    apply False.elim h54
  -- Implications on the right can always be decomposed.
  intro h55
  -- Disjunctions on the left can always be decomposed.
  cases h55
  case inl h56 =>
    -- Conjunctions on the left can always be decomposed.
    let h57 := h1.left
    let h58 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h57
    case inl h59 =>
      -- We want to use the implication h59 based on <expert-advice>. So we show its premise.
      have h60 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h59, we can now drive its conclusion.
      let h61 := h59 h60
      -- False on the left can always be used.
      apply False.elim h61
    case inr h62 =>
      -- False on the left can always be used.
      apply False.elim h62
  case inr h63 =>
    -- Conjunctions on the left can always be decomposed.
    let h64 := h1.left
    let h65 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h64
    case inl h66 =>
      -- We want to use the implication h66 based on <expert-advice>. So we show its premise.
      have h67 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h66, we can now drive its conclusion.
      let h68 := h66 h67
      -- False on the left can always be used.
      apply False.elim h68
    case inr h69 =>
      -- False on the left can always be used.
      apply False.elim h69



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357972063187441127584934764360 : (p5 → (False ∨ ((((((p2 ∨ p4) ∧ p5) → p2) → (p1 → ((((p2 ∧ (p2 ∧ p1)) ∨ (p3 ∨ True)) ∨ (p1 ∨ False)) → p4))) ∧ True) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693648694545572495468507431558 : ((((((p1 ∨ ((True ∧ (p2 ∨ p3)) ∧ ((p1 → p5) ∧ p1))) → False) ∨ True) ∨ (((((p5 ∨ True) → False) → p5) ∨ False) ∧ (p2 → p2))) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_618213538804653192909732970270 : ((((((p1 → (p1 → p1)) ∧ p4) ∨ ((((False ∨ ((p2 ∨ p4) ∨ p3)) ∧ ((p4 → p1) ∨ (p4 ∨ False))) → p1) ∧ (p1 → p1))) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_215853653959304990469435579740 : ((p2 ∨ (p4 ∧ (p2 ∨ p1))) ∨ (((p3 ∧ p1) ∨ ((p5 → (p4 ∨ (p2 → (p5 → False)))) → ((p5 ∧ False) ∧ ((p2 ∨ p5) → True)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165901224611352053339194904645 : (((False ∨ (p2 ∨ True)) → ((((p1 ∨ True) → True) ∧ p5) → (p2 → (p4 ∧ (False ∨ p4))))) ∨ ((p2 ∧ (p3 ∨ p3)) ∨ (True ∧ (True ∨ True)))) := by
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
theorem thm_5_vars_263102031994671640418039026578 : (True ∧ ((((p1 ∧ (p2 ∨ (p4 → ((p3 ∧ p1) ∧ (p5 ∨ (p3 ∨ (False ∨ ((p4 ∧ True) ∨ p3)))))))) → p4) ∨ (p2 → p2)) ∨ (p3 ∨ p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315026282522250215190730962347 : (p3 ∨ ((p2 ∧ (((False ∨ (False ∨ False)) ∨ p4) ∨ False)) ∨ (((True ∧ (((p3 ∨ True) ∧ True) ∨ ((True → p2) ∨ p2))) ∧ False) → (False ∨ p1)))) := by
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
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h3
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h3
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- False on the left can always be used.
      apply False.elim h3
    case inr h13 =>
      -- False on the left can always be used.
      apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_804661369685594558897687871426 : (((p3 → (((p5 → p2) → (p4 ∨ p2)) → (((True → p1) → (((p3 → (((True → False) ∨ (True ∨ p2)) → p5)) ∧ p5) ∨ False)) ∨ p3))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58495964665293442197715956753 : (((p4 ∨ p3) ∧ ((p4 ∧ (((False ∧ (((p1 ∧ (p5 ∧ (p2 ∨ ((p5 ∧ p1) ∨ p4)))) → p4) → p3)) ∨ (True → p5)) ∧ p2)) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622230786045437443003937985954 : ((((p2 ∧ (p4 ∨ ((True → p5) ∧ ((True ∧ ((p3 ∨ (False ∧ p5)) ∨ (p4 → ((True ∨ (p4 ∨ p3)) ∨ p4)))) ∨ (p4 ∨ p2))))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_603560533010238069754820916367 : ((((p3 ∨ (True ∧ ((p4 ∧ (p1 ∨ p4)) ∨ (p1 ∧ (p1 ∧ ((p4 ∨ (p2 → p4)) ∧ (p2 → (True ∧ (p5 ∧ (p4 ∨ p3)))))))))) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357262051771693127023450920322 : (p5 → ((p2 ∧ False) ∨ (((((p3 → ((((p5 → p5) ∨ p1) ∨ p3) ∧ (p1 → (False ∧ p3)))) → p3) ∧ p5) ∨ (True → False)) ∨ (False → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40378142012247498445430056333 : (((((((False → p5) ∧ ((p2 ∧ p1) ∨ p1)) ∧ ((p4 ∧ (p2 ∧ p5)) → (True ∧ (p3 → (False → False))))) ∧ (p2 ∧ True)) ∨ p4) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115114853470774246189770199965 : ((((p2 ∨ (p3 ∧ (False → ((p5 → p1) → (p3 ∨ False))))) → True) → (((p1 → True) → (True ∧ (p5 ∨ False))) → (p3 ∨ p3))) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60331579771750241616798490417 : (((p2 → False) → ((p3 ∨ (p4 ∨ p2)) ∧ (p1 ∧ ((p1 ∨ (p1 ∨ (p1 ∨ (((False ∨ p1) ∨ (p4 → p4)) ∨ (True → True))))) ∨ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654633265682174570231590188556 : (((((p4 → (p4 ∧ ((p4 ∨ ((p1 ∧ p5) ∧ p2)) → ((p4 ∧ ((p5 ∨ (False ∧ (p1 ∧ p1))) ∧ p2)) ∨ p2)))) ∨ p2) ∨ (True → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705767405270914789222626434081 : (((((((p2 ∨ p4) ∧ p3) ∧ p3) → (p5 ∨ p1)) ∧ ((p2 ∧ (((p4 ∨ (p5 ∨ (p5 ∧ (p4 ∧ False)))) ∧ p3) → False)) ∧ (p4 ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318864159555542160569276564780 : (p4 ∨ (((p4 ∨ (((((p4 → (p3 ∧ True)) ∨ (True ∧ p2)) → False) ∧ (True → p4)) → (False ∧ True))) ∧ (p5 ∧ p4)) ∨ ((p4 ∧ p4) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164573025460183024792833956168 : (((((p2 ∨ p4) ∧ p3) ∨ (True → (p1 ∨ (False ∨ ((p1 → p3) ∨ (True ∧ p1)))))) ∧ False) ∨ ((True ∨ (p5 ∧ p2)) → ((False ∧ p4) → False))) := by
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
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56476990474469184564620994427 : ((((p2 → p2) → (False ∧ False)) → (True ∧ (((p5 ∨ (False → ((p5 ∨ p5) ∨ (p5 ∨ (p3 → ((p2 ∨ True) → p1)))))) → p1) ∨ True))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_683667721498580174803190975672 : ((((((p1 → False) ∧ (((p1 ∨ p4) ∧ p5) ∧ (p2 ∨ (p3 → (p4 ∧ (p5 ∧ p5)))))) ∧ p3) ∨ ((False ∨ (False ∨ (p5 ∧ p3))) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185470162842648838830489563537 : ((p1 ∨ (((False → p2) ∧ (p3 ∨ p1)) → (p3 → (False ∨ p1)))) ∨ (False ∨ ((p4 ∨ p5) ∨ (((p1 ∨ (p2 → False)) ∨ p2) ∨ (False → p3))))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662614884006169757668685214 : ((((((((p3 ∧ p1) ∧ p4) → (p5 ∨ (p3 ∧ p5))) ∨ p4) ∨ p3) ∧ (p5 ∧ (p3 ∨ p4))) ∨ (p3 ∨ ((True → False) → p1))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_666795784998395480848610470126 : (((((((True ∨ p1) → (True ∨ p2)) → (True → p1)) ∨ (p4 ∨ (p1 ∨ ((p3 ∧ (p2 ∨ p3)) ∧ (p5 → p1))))) ∧ (True ∨ (p1 ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149944572986714348493696668603 : ((p3 ∨ (p1 ∨ ((p2 ∨ (p3 ∨ (((((p3 → (True → p3)) → p4) ∧ p2) → p1) → (p5 ∧ True)))) ∨ False))) ∨ ((False ∧ (True → p3)) → False)) := by
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
theorem thm_5_vars_56729590325420350711419705019 : ((((p3 ∨ True) ∨ p5) ∧ (p2 → (p4 → (((p4 → p1) ∧ False) ∨ (p1 ∨ ((((p1 → (p2 ∧ p3)) ∧ (p5 ∨ p5)) ∨ p1) ∨ p4)))))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_650172456925994062752271932961 : (((((True → ((((p5 ∧ (False ∧ (p5 ∧ True))) ∧ (True → p5)) ∧ (False ∨ p2)) ∨ p1)) ∧ ((False ∧ p3) → (True ∨ p3))) ∧ (p4 ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_791430063662628517944084475970 : (((True → (((p1 ∧ (p1 ∧ p5)) ∨ ((p2 → (p4 ∧ (((p3 ∨ (((p2 → p3) ∨ p3) ∨ True)) → p5) → False))) ∨ (p5 ∧ True))) ∨ True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_787401510259456046080614460210 : (((p4 ∨ (p4 ∧ ((((p4 ∧ p2) ∨ p2) ∨ p3) → ((p3 ∧ (False → (p5 ∨ (p5 → (p4 ∨ (True ∧ p5)))))) ∧ ((p4 ∨ p5) ∨ p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256830632162764738614241228903 : ((p1 ∨ p3) → ((((False ∧ ((True ∧ (p2 ∨ p1)) ∧ p5)) ∧ ((True ∨ (((p4 ∧ p5) ∨ False) ∧ p2)) ∨ p5)) ∨ (p3 ∨ True)) ∧ (p1 → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337278696216949679565426317007 : (p1 → ((((((p3 ∧ ((True ∨ p5) ∧ True)) → (p4 ∨ (p5 ∧ (p4 → p5)))) ∧ p4) → (p5 ∧ (p5 → p3))) ∨ True) ∧ (p3 ∨ (False → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118335787591102027178216880426 : ((p2 ∨ ((((((p4 ∨ p5) ∨ p1) → p3) → ((p2 → (p3 ∧ (p1 ∨ (p2 ∧ ((p1 ∨ p4) → p1))))) ∧ p2)) ∧ p3) ∨ True)) ∨ (False ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314663278445160736030218198721 : (p3 ∨ ((p4 ∧ (((p4 → True) ∧ (p1 ∨ p5)) ∧ (False ∨ ((p3 → (False → p5)) ∨ p1)))) ∨ (p4 ∨ ((((p3 ∨ p5) → p5) ∨ True) ∨ p3)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196823486068795902133271360523 : (((p1 ∧ (((p3 → True) → True) → p4)) ∧ p1) ∨ (((p2 → True) → p1) ∨ ((p1 ∨ True) → (((p4 ∨ (p2 ∧ p2)) ∧ (p2 ∧ False)) → False)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h4.left
    let h12 := h4.right
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51127339071128730713268268451 : (((((p1 → p1) → (((p1 → (((p2 → (False ∧ p2)) ∧ p2) → p2)) ∧ p3) ∨ p4)) ∨ True) ∨ (p3 ∧ (False → ((p4 ∧ p4) ∧ p1)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44232647952417120498032241336 : (((((p5 → ((p1 → (p2 ∨ (p3 ∧ p4))) ∨ p1)) ∨ (((False → p5) → (p3 → p3)) ∧ p4)) ∨ (p5 ∧ ((p3 ∧ False) → p1))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_791553069403372955703578145907 : (((True → ((((False ∨ p2) → (((p4 → ((p4 → p4) ∨ True)) ∨ (True ∧ (p2 → (p4 ∧ (p1 ∧ (p1 → p4)))))) → p3)) ∧ p2) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55564085109338055322998522240 : (((p5 ∧ ((p3 ∨ (False ∨ p1)) ∧ p4)) → ((p1 → True) → ((p5 ∧ (True ∨ (((False → p5) → p1) ∧ (p5 ∧ p1)))) → (p4 ∧ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350084611443434778831007278749 : (p4 → (((p5 ∨ (((((p5 ∨ ((p2 ∨ (False → ((False → p3) ∧ True))) ∨ p1)) ∨ p5) ∧ (p4 → p4)) ∧ p2) ∨ False)) → (p3 ∨ p2)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50643420059662432472790465625 : ((((p1 ∨ ((False ∨ ((p2 ∧ True) → p3)) ∨ ((p2 → p1) ∨ p5))) → ((p2 ∧ p5) ∨ (p3 ∧ p4))) → (((p4 ∨ p2) → False) → False)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (p1 ∨ ((False ∨ ((p2 ∧ True) → p3)) ∨ ((p2 → p1) ∨ p5))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : (p4 ∨ p2) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- False on the left can always be used.
    apply False.elim h6
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h3
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h11 : (p4 ∨ p2) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h12 := h2 h11
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h16 : (p4 ∨ p2) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h15
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h17 := h2 h16
    -- False on the left can always be used.
    apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118549335427450917420761634073 : ((p3 ∨ (True → (((((False → (((False ∨ ((p1 ∨ (p5 → p3)) ∧ p3)) ∨ (p3 → p3)) → True)) → p3) ∨ p3) ∨ p3) ∧ False))) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721475796641900894583603835459 : ((((p2 ∧ ((p5 ∧ False) → True)) → (p4 ∨ (p1 ∨ ((((True → p5) → (False ∧ p3)) ∧ (p4 ∧ p3)) ∧ (p1 ∨ (p1 ∨ (p5 ∧ p5))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_31685985570063060831837471635 : ((False ∨ (((((p3 ∨ (p2 ∨ True)) ∨ p2) → ((p5 ∧ p5) ∨ False)) ∧ ((p5 → (p4 ∨ p1)) ∨ (p3 → p4))) → (True ∧ (p5 ∨ p2)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : ((p3 ∨ (p2 ∨ True)) ∨ p2) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h12 : ((p3 ∨ (p2 ∨ True)) ∨ p2) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h13 := h2 h12
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h16
    case inr h17 =>
      -- False on the left can always be used.
      apply False.elim h17
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167671846137400076211992580882 : (((False → ((p5 ∧ ((p4 ∧ (((p1 → False) → p3) ∧ p4)) ∧ p2)) ∨ p2)) → (p2 ∨ p2)) → (((False ∧ True) ∨ p2) ∨ (True ∧ (p5 ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → ((p5 ∧ ((p4 ∧ (((p1 → False) → p3) ∧ p4)) ∧ p2)) ∨ p2)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183845643635963422722058722392 : ((((((p2 → p5) → True) → (True ∧ p5)) ∨ (p1 ∧ False)) ∧ p4) ∨ (((True → False) ∨ ((p5 ∧ p4) → ((p3 → p5) ∧ p4))) ∨ (p5 ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215752205975393103454478119240 : ((p1 ∨ ((p4 ∨ False) ∧ False)) ∨ (((((p5 → False) ∨ (p3 ∨ p4)) ∧ p1) → p2) ∨ (True ∨ (False ∧ (((False ∨ p1) → (False → True)) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346768445303155052907222594207 : (p3 → ((((False ∨ False) ∧ (p2 ∨ (((True ∨ p4) → ((p4 ∨ ((p5 → p2) ∧ False)) ∧ True)) → p1))) ∨ p2) ∨ (False → ((p4 ∧ p1) ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209051491432245809512588987719 : ((p1 ∨ ((p3 ∧ (True ∨ True)) → p1)) → (((True → False) ∧ (((((True ∨ True) ∨ True) ∨ (p3 ∨ p5)) → ((p1 → p1) ∧ p3)) ∧ p5)) → False)) := by
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
  cases h1
  case inl h7 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h9 := h3 h8
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h11 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h12 := h3 h11
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_88829676584090175521775716761 : ((((p1 ∨ True) → (p1 → p1)) → ((p2 → (p2 ∧ (((p5 ∧ False) → (True ∧ (False ∨ (p3 ∨ (p4 → False))))) ∨ (p5 → p1)))) ∧ p3)) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p1 ∨ True) → (p1 → p1)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- One of the premise coincides with the conclusion.
      exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h2
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h8



