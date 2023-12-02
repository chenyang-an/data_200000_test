variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51831112723959291093485668792 : (((p4 → (True ∨ ((False → (((p3 → p2) ∨ (p1 ∧ (p3 → p2))) → False)) ∨ False))) ∧ ((((p5 ∧ p4) ∨ p2) ∨ (False ∨ p3)) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255833124235054225991781103517 : ((True ∨ False) → (p2 ∨ (((((p4 ∧ p5) → True) → ((p5 ∧ False) ∨ p4)) ∨ (True ∨ True)) ∨ (((p1 ∨ ((False → True) → p4)) ∨ p4) → True)))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258056151339138712638224725306 : ((p4 ∨ p2) → (((p2 → ((((p4 ∧ (p5 → False)) ∨ p4) → p4) ∧ (p2 ∧ p5))) → p4) ∨ (False ∨ ((True → (p5 ∨ p2)) ∨ (p5 ∧ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179618931236299853120678654123 : ((p4 → ((False ∧ ((((False ∧ (p3 ∨ p4)) ∨ False) ∧ p5) ∧ p5)) ∨ True)) ∨ ((((p2 ∧ (False ∨ p3)) ∨ ((p5 → p5) ∨ p4)) ∧ True) → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624063970572750566095892865427 : ((((p2 ∨ ((False ∧ ((p2 → p5) ∧ (p5 ∨ p1))) ∧ (p1 ∨ (((((p5 ∧ p2) → p3) → p5) ∨ False) ∧ ((False → p4) ∨ p1))))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_802021708312762578682978753383 : (((p2 → ((p2 ∨ p2) → (((p5 ∨ False) ∧ ((((p2 ∧ (True ∧ False)) ∧ (True ∨ False)) ∧ p5) ∨ (p5 → (p5 ∧ p5)))) ∧ (p3 ∧ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320342627908314454472917557663 : (p4 ∨ ((True → p4) ∨ ((p2 ∨ (((p4 ∨ ((((True ∨ True) → p5) → p2) → p4)) → (True → p3)) ∨ ((True ∧ (p4 → p2)) ∨ False))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60367408171141909823151166154 : (((p3 → True) → (p4 → (((((((False ∧ False) ∧ True) ∧ (p3 ∧ True)) ∧ p1) ∧ (True → p5)) ∨ p4) ∨ (((p3 ∨ p3) → p5) ∨ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251465109895324870706897473481 : ((p2 → p5) ∨ (p1 → ((((((False ∧ (True → p2)) ∨ p5) ∧ ((p4 ∨ (True ∧ (p2 ∧ True))) → False)) ∧ ((False ∧ p3) ∧ p3)) ∨ p1) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60640118955177478884897565897 : ((True ∧ (((((p5 → (((p1 → False) ∨ p5) ∧ (p1 ∨ False))) ∨ True) ∧ p2) → (p4 → ((p3 ∧ p2) ∨ p1))) ∨ (p3 → (p2 ∨ True)))) ∨ p4) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_587183766194795327702728055304 : (((((p4 → (False ∨ (True → ((p5 → False) → ((p4 ∧ ((p2 → p2) → ((((p5 → False) → p3) → p1) ∨ False))) → p2))))) ∧ p2) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201068143359737812821032105476 : ((p5 ∨ ((True → ((p5 ∨ True) ∨ p4)) → False)) → (((p5 → (p4 → (((((False ∨ p1) → p5) ∧ p2) ∧ p2) ∨ p3))) → p2) ∨ (p5 ∧ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : (True → ((p5 ∨ True) ∨ p4)) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h4
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56374770405201286239851995723 : (((((False ∨ p5) ∧ p3) → p1) → ((p3 ∨ (p5 ∨ ((((p4 ∨ (True → True)) ∧ p1) → (p2 → (p4 ∨ p1))) ∧ p4))) ∨ (p3 ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614599030157998141975478344291 : (((((p1 ∧ ((p1 ∨ ((p1 → p1) ∧ ((p5 ∧ (p2 ∧ ((p1 ∨ p4) → p1))) → p3))) → p4)) ∧ ((True ∨ p1) → (False → True))) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_65794915934498025433859102479 : ((p4 ∨ (((((p4 ∨ p1) ∨ (True ∧ True)) ∨ p1) ∨ (p4 ∧ True)) ∧ ((p5 ∨ (True ∨ ((True → (p5 → p3)) ∧ p4))) → (p2 ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40903854451222717426494558571 : ((((True ∧ (((((p2 ∨ True) → (True ∨ p4)) → (((p5 ∧ (p2 → False)) → p1) → False)) → (p4 ∨ p4)) → p4)) ∧ (p4 ∨ p1)) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138806815615458139237061221874 : (((True ∧ (False ∨ ((p4 → p2) ∧ ((True ∨ p2) ∧ (((((p2 ∧ p2) → p1) → (p4 ∨ p1)) → p2) ∧ p5))))) ∧ p5) → (p4 ∨ (p1 → p2))) := by
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
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h11.left
      let h14 := h11.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h15
      -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
      have h16 : (((p2 ∧ p2) → p1) → (p4 ∨ p1)) := by
        -- Implications on the right can always be decomposed.
        intro h17
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h15
      -- We have shown the premise of h13, we can now drive its conclusion.
      let h18 := h13 h16
      -- One of the premise coincides with the conclusion.
      exact h18
    case inr h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h11.left
      let h21 := h11.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h22
      -- One of the premise coincides with the conclusion.
      exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43957557026816198336458759186 : ((((True ∧ (p5 → ((False ∧ (p4 ∨ p2)) ∧ ((p1 ∨ p3) → ((p3 ∧ (((p4 ∧ p1) ∧ p1) → p4)) ∨ p3))))) ∨ (p1 ∧ p2)) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138061922666799457597008193463 : ((True → (False ∨ (p4 ∧ ((True ∨ ((p5 → False) → p5)) → ((p3 → p3) ∨ ((False ∨ ((p3 → p1) ∨ p5)) ∨ p1)))))) ∨ (p5 → (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712752362355325985864706348534 : (((((False ∨ p4) ∨ ((p4 ∨ p3) ∧ True)) ∨ ((p2 → ((True ∨ (p5 ∧ ((True → p4) → True))) ∧ ((p2 ∧ p5) ∨ p1))) ∨ (p5 → True))) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_729998184325711919378713251628 : (((((True ∨ p2) → p3) → (False ∧ (p5 ∨ (((((p3 → p5) → (p2 ∧ (p2 → p2))) ∧ ((False ∨ p5) → (p1 ∧ False))) ∧ p4) ∨ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68509165351439553416175989199 : ((p3 → (p4 ∨ ((True ∨ (((p4 ∨ (False ∧ p5)) ∧ p1) ∨ ((p1 ∨ p1) ∧ p5))) → (True ∧ (p2 ∨ ((p3 ∨ p3) ∨ (True ∨ p5))))))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- False on the left can always be used.
        apply False.elim h10
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41199835230789670004351872657 : ((((p1 ∧ (p2 → (p4 ∧ (p3 ∧ (((True ∧ (p5 → p1)) ∧ (p4 ∨ p2)) → ((p5 → False) ∨ p3)))))) → ((p5 ∧ p3) ∨ p3)) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234210998691636389693856936270 : ((False → (p4 ∧ False)) → (p1 → ((((p3 ∨ (False ∨ p2)) ∧ p1) ∨ ((True → p3) → False)) ∨ ((p1 ∨ (True ∧ p4)) ∨ (False ∧ (p5 ∨ p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172559336320649302510865247199 : (((p1 ∧ (p3 ∧ p2)) ∨ ((p4 ∧ (p2 ∧ (((p5 → p4) → p4) → p3))) → False)) ∨ ((((p4 ∧ p1) ∨ p5) → (p5 ∨ (p2 → p4))) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354781160242116998630339611323 : (p5 → ((((p1 ∨ False) ∨ (((p4 → p2) ∨ p3) ∧ p1)) ∧ (p3 → (p5 → (True ∧ (p4 ∨ ((p5 ∧ p4) → ((p3 ∨ p5) ∨ p5))))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111918520177691269239312985679 : ((((p4 ∨ (((True → p5) ∨ (p2 → (p3 ∨ p3))) ∧ (p5 ∧ p3))) ∨ (((p3 ∨ p3) ∧ p5) ∧ (p2 ∧ (p2 ∨ p4)))) ∨ True) ∨ (True → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_685430682631311185681816652753 : (((((((True ∧ (True ∧ p4)) ∨ ((False ∨ (False ∨ (p4 → (p5 ∧ p5)))) ∧ p1)) → p5) ∧ p1) → (False ∧ (p5 ∨ (p2 → (p4 → False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677610694873322334832821199457 : (((((((p3 ∨ ((True ∧ (True → (p3 ∧ p1))) ∧ (p2 ∧ p2))) → ((p4 ∨ False) → True)) ∨ True) → p2) ∨ (False → ((True → p1) → p1))) ∨ False) ∧ True) := by
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
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168579138130720945861212711396 : ((p2 ∧ (((p5 → p2) ∨ (((True ∨ p4) → False) ∧ (p1 → p5))) ∨ ((True ∧ p3) ∧ False))) → (((p5 ∧ (p4 → p5)) ∧ p3) ∨ (p2 → True))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h12.left
    let h15 := h12.right
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689501177901247884055366747299 : (((((p3 → ((((p5 → True) ∨ (p5 ∨ p2)) → p2) ∨ False)) → (p1 ∧ (p1 ∧ p2))) ∨ (((p5 → (p1 → p1)) ∨ (p5 ∨ p5)) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116513303658136473155669455966 : (((p4 ∧ p4) ∧ (p2 ∨ (((((True → False) ∨ p3) ∨ p3) ∨ True) ∨ (((p1 ∧ (((p3 → p5) → False) → True)) ∧ p1) ∧ p4)))) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304094674638660096977722184025 : (p1 ∨ ((True → (p1 ∨ ((((p2 ∨ False) ∧ p4) → p4) → ((((p2 ∧ ((p5 → False) → True)) ∧ p2) ∧ p5) ∨ ((p2 ∨ True) ∨ p2))))) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341674781995707833128746501931 : (p2 → (((((p5 ∨ True) → p4) → ((p1 ∨ (p5 → ((p4 → p1) ∧ ((p5 ∧ False) ∧ ((p3 → p4) → p4))))) ∨ p4)) ∨ p4) ∨ (p3 → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p5 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159921380427251902995513959940 : ((((((p1 ∧ ((((True ∨ True) ∧ p3) ∨ (p1 ∨ True)) ∨ False)) ∧ p3) → (p1 ∨ False)) → p4) → False) → ((False → p3) → (p4 ∨ (False ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698671447324120693315139437575 : (((((p1 ∧ (p3 → True)) → (((p3 ∧ True) ∨ p2) ∨ (True ∧ p4))) ∨ (p1 → ((p4 ∨ p1) ∨ ((True ∨ (False ∨ (p5 ∨ p5))) ∧ p2)))) ∨ p3) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200605036715571218780530772851 : ((True ∧ (p3 → (((p5 → False) ∧ True) ∨ p1))) → (True → ((False ∨ (((p4 ∨ ((p1 ∨ p4) ∧ (p4 ∧ p5))) ∨ True) → p5)) ∨ (False → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347367047577496309884936259134 : (p3 → (((p5 ∧ ((p4 → (p2 ∨ p5)) ∧ True)) ∧ p4) ∨ (((p5 ∧ True) ∨ True) ∨ ((False ∨ p2) ∨ ((False ∨ (p1 ∨ (p2 ∨ p3))) → p2))))) := by
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
theorem thm_5_vars_41580938934034263477863497706 : ((((((p2 ∧ (p5 ∧ p5)) ∧ p1) ∨ (p3 ∨ True)) ∧ ((((True ∧ p4) → (False ∨ (p1 ∧ True))) → True) ∨ ((p1 ∧ p1) ∨ p4))) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738206094414227783272410393282 : ((((False ∧ p3) ∨ ((p1 ∨ ((p5 ∨ p4) ∧ (False → p2))) → ((p3 ∧ (((False ∨ True) ∨ False) → (p2 → p2))) ∨ ((True ∨ p3) ∧ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339970323955491962964912336761 : (p1 → (p1 → ((p3 ∨ ((True → (p4 ∨ (True ∧ p4))) → (((p1 ∧ False) ∧ ((((p5 ∧ p1) ∨ p1) ∧ (p2 ∨ p3)) → p5)) ∧ p4))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184635535340820606036448302874 : (((p3 ∨ (((p1 ∧ p1) → False) ∨ p4)) ∧ (p3 ∧ (False → p1))) ∨ (((((False → (p4 → p3)) ∧ p4) ∧ ((p4 → p3) ∧ p2)) ∧ True) → p3)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h5.left
  let h9 := h5.right
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h10 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h11 := h8 h10
  -- One of the premise coincides with the conclusion.
  exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_572286924663163648856243886 : ((((p4 ∨ ((False → (((((True ∨ (((p1 → p3) ∧ p2) → (p1 ∧ False))) ∧ p4) ∨ True) ∨ p4) → p2)) ∨ p3)) ∨ p5) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_810980356827118033514351066835 : (((p5 → ((p4 → True) → (((True ∧ (((False → True) ∨ p4) ∧ ((p3 → (False ∧ (p4 → (p4 ∧ (True ∧ False))))) → p3))) ∧ p2) ∨ True))) ∨ p5) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164620887813243604147214265056 : (((p5 ∧ (((p4 ∧ p3) → (False → (((p5 ∨ p2) ∧ p4) ∨ (False ∨ True)))) → p1)) ∧ p5) ∨ (((p4 ∧ (p5 ∧ True)) ∧ (True → p4)) → p5)) := by
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
  let h6 := h5.left
  let h7 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_603625495246984678051690307040 : ((((p3 ∨ (p3 → (((p5 ∨ ((False → p5) ∧ True)) → ((p5 ∧ p2) → ((p3 ∧ ((p1 ∨ False) → False)) ∧ True))) ∧ (p1 ∧ True)))) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_688458914821314550848461955862 : ((((p4 ∧ ((((p4 ∨ (p4 → ((p5 → False) ∨ p2))) ∨ p1) ∧ True) ∨ (False → True))) ∧ ((((False → (True ∨ p3)) ∧ p2) ∧ p3) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173164980685694176046718163598 : ((p4 ∨ (((((p1 ∨ (p4 ∧ p5)) → p1) → (p5 ∧ (p5 ∨ p1))) ∨ p2) ∧ True)) ∨ ((p4 ∨ True) ∧ (((p3 → p3) ∨ (p3 ∧ False)) ∨ p4))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655467060456081842952940628574 : (((((p3 ∨ ((((p3 ∧ p3) ∨ ((p1 ∨ (p2 → (p4 ∨ False))) → True)) ∧ (p5 ∨ (p4 ∧ True))) → p2)) ∨ (p2 ∧ p3)) ∨ (p3 → p3)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355576032530841520637324133594 : (p5 → (((p4 ∧ (p1 ∨ ((p2 ∧ p4) → (((p4 ∧ ((False ∨ p2) → p5)) ∨ p3) → p3)))) ∨ (p1 ∧ ((p4 ∨ True) ∨ p2))) ∨ (p3 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225046642385498186080963301614 : (((False ∧ p5) ∧ p2) ∨ ((p4 ∧ (p3 ∧ (True → False))) → (p3 → (((p3 ∧ True) ∨ p4) ∧ ((p1 ∧ p2) ∧ (p3 → ((True ∧ p5) ∧ True))))))) := by
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
  let h5 := h4.left
  let h6 := h4.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
  have h11 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h10, we can now drive its conclusion.
  let h12 := h10 h11
  -- False on the left can always be used.
  apply False.elim h12
  -- Conjunctions on the left can always be decomposed.
  let h13 := h1.left
  let h14 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h15 := h14.left
  let h16 := h14.right
  -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
  have h17 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h16, we can now drive its conclusion.
  let h18 := h16 h17
  -- False on the left can always be used.
  apply False.elim h18
  -- Implications on the right can always be decomposed.
  intro h19
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h20 := h1.left
  let h21 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h22 := h21.left
  let h23 := h21.right
  -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
  have h24 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h23, we can now drive its conclusion.
  let h25 := h23 h24
  -- False on the left can always be used.
  apply False.elim h25
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256170683374514438546500546711 : ((False ∨ True) → ((p4 ∨ ((((p3 ∨ ((False → p5) ∧ (True ∧ ((p2 ∨ p5) → p2)))) ∨ False) ∨ p4) ∨ True)) ∨ (p4 → ((p4 → p2) ∧ p4)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179483600886289331835909929881 : ((True → ((False → (True ∨ True)) ∧ (((p4 → (False → False)) → p4) ∨ False))) ∨ (((((p2 ∨ (p5 → True)) → (False ∧ p2)) ∨ p1) ∨ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185770904283514509392206731608 : ((p4 → (((p4 ∧ p3) → False) ∧ ((p4 ∨ (True ∧ p3)) ∧ p1))) ∨ ((p4 → p4) ∧ (p3 → (((True ∧ (False ∨ (False ∧ p4))) ∧ False) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322602737647408856694559374123 : (p5 ∨ ((p2 → ((p1 ∧ p4) ∨ ((p2 → (p2 → ((p4 ∧ p4) ∨ p3))) → ((p1 ∨ p3) ∧ ((p5 ∨ (False ∨ (p1 ∧ p4))) → p3))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_20169620783277955166247253967 : (((((p3 ∧ (False ∨ (p2 ∨ p4))) ∨ ((p2 ∧ (p5 → p4)) ∧ p1)) ∨ p2) ∨ (((True → p5) ∨ p1) → (True ∨ (p1 ∨ (p2 ∧ False))))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216263209241690986823817130881 : ((p1 → (p5 ∨ (p4 ∨ p5))) ∨ (((((p5 ∨ (p4 ∨ p2)) ∨ (p3 ∨ ((p4 ∨ (True → p3)) ∧ ((True ∨ True) ∧ p1)))) ∧ True) ∨ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328348034812297136733529131832 : (True → (((p3 ∧ False) → ((True → ((p4 → (p1 ∨ (True → p3))) → ((p5 ∨ (p4 → False)) → p3))) ∨ p4)) → ((p5 → (p2 ∧ p2)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117457334478132535425384768030 : ((p1 ∧ ((True → p3) ∧ (((p2 ∨ (p4 ∨ p2)) → ((True ∧ (p2 → p3)) ∨ False)) ∨ (p3 ∧ (((False ∧ p1) ∨ p5) ∨ p5))))) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199339966085589606373636773009 : (((((p3 → p3) ∨ (p4 → p3)) → p2) ∨ False) → ((((p1 → p5) ∨ p5) ∧ p3) ∨ (((p2 → (p3 ∨ p1)) → (p4 ∨ (True ∨ p3))) → True))) := by
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
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_754256444551260725661233306653 : (((False ∧ ((p2 ∨ p4) ∧ ((p4 → (True ∧ (((p1 → (p2 ∧ (True ∧ (p2 ∨ False)))) ∧ (p4 ∨ p5)) ∨ p3))) → ((p5 ∧ False) ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172670363417222835996315727077 : (((p3 → p1) ∧ ((((((p5 → p5) → p4) → (p3 ∧ p1)) ∨ p5) ∧ p3) ∨ p2)) ∨ (False ∨ (p1 → ((False ∨ (p1 ∧ (p3 → p5))) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789476668047025899470011496630 : (((p5 ∨ (((p2 ∧ ((p5 ∧ (p4 ∨ (p3 → p1))) ∨ (p5 ∨ p5))) ∧ p3) → ((((p5 → True) ∨ (p5 ∨ True)) ∧ (False ∧ False)) ∨ p2))) ∨ p1) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252750628714902910967017830054 : ((True ∧ True) → (((((p3 → ((p4 ∨ (False ∧ (True → p5))) ∧ ((((p5 → p2) ∧ False) ∧ False) ∧ p2))) ∨ (p2 → p2)) → p4) ∨ p3) ∨ True)) := by
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
theorem thm_5_vars_115936556374678528809701903485 : (((p5 ∧ ((p4 ∨ p3) ∧ False)) ∨ ((((p2 ∨ (False ∨ p3)) ∨ p1) ∨ (p4 ∨ ((p4 ∧ False) ∨ (True ∨ p3)))) ∧ (p1 → False))) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_98823946964612455788857281654 : ((True → ((p4 ∧ (((p1 ∧ (p4 → (True ∨ ((p2 ∧ (p1 ∧ p3)) → (p2 ∨ p1))))) ∧ ((p3 ∨ p3) ∧ p5)) ∧ (p4 → p3))) ∧ p3)) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112883588430932269187309593952 : ((((p3 ∧ p3) ∧ ((p2 ∨ (p5 ∨ (p2 ∨ ((False ∨ (True ∨ (p4 ∨ (p2 ∨ p1)))) → p4)))) ∧ (p2 → (True ∧ p1)))) → p2) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260605466204693249229622346333 : ((p3 → p2) → ((((p4 ∨ p4) → (False ∧ p4)) → (p5 → (((p5 → False) ∧ (p5 ∧ p5)) → False))) ∨ ((p2 ∧ False) → ((False ∨ p5) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_716222866164502991193569032230 : (((((p3 ∨ (p2 ∨ p4)) → p2) ∧ (((((p2 ∨ False) → p4) ∧ (True ∧ (True ∨ False))) ∨ True) → (((True ∧ p4) ∧ p5) ∨ (p5 ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119570211097640719365739448825 : ((p5 → ((False ∨ ((p1 ∨ p1) ∧ (p4 ∨ p2))) ∨ (((p5 ∧ p2) ∨ p1) → (p2 → (((True ∧ p4) → p3) → (p2 ∨ p3)))))) ∨ (p3 ∨ p4)) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_98948650421481177928558384287 : ((True → ((p1 ∧ ((p1 ∧ p5) ∧ (True ∧ (((False ∧ (p2 ∧ p5)) ∨ p3) ∧ ((p4 ∧ (False ∧ p3)) ∧ p2))))) ∧ ((p5 ∨ p1) ∧ p3))) → p3) := by
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
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50361920458491584084814272202 : (((((p3 → p5) → p2) ∧ ((p1 ∧ (True ∧ False)) → ((p4 ∨ ((True ∨ p5) ∧ (True ∧ p2))) ∧ p4))) ∨ ((p2 → False) ∨ (p4 ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301965581472218851780879038907 : (False ∨ ((True → False) → ((p3 ∧ (True ∧ (((p1 ∨ (p2 → p4)) ∧ p5) ∨ p3))) → (p2 ∨ (p1 ∧ ((p3 → (False ∧ (p4 ∧ p3))) ∧ True)))))) := by
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
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h11 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h12 := h1 h11
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h14 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h15 := h1 h14
      -- False on the left can always be used.
      apply False.elim h15
  case inr h16 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h17 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h18 := h1 h17
    -- False on the left can always be used.
    apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160144654612053754253280142610 : ((((p1 ∨ (p3 ∨ ((p3 ∨ (False ∨ (((p4 ∧ False) ∨ p5) ∧ p3))) → p3))) → p2) ∧ (p2 → False)) → (((False ∨ p1) → False) ∧ (p5 ∧ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h1.left
    let h6 := h1.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : p2 := by
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h8 : (p1 ∨ (p3 ∨ ((p3 ∨ (False ∨ (((p4 ∧ False) ∨ p5) ∧ p3))) → p3))) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h9 := h5 h8
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h10 := h6 h7
    -- False on the left can always be used.
    apply False.elim h10
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h11 := h1.left
  let h12 := h1.right
  -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
  have h13 : p2 := by
    -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
    have h14 : (p1 ∨ (p3 ∨ ((p3 ∨ (False ∨ (((p4 ∧ False) ∨ p5) ∧ p3))) → p3))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h15
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- One of the premise coincides with the conclusion.
        exact h16
      case inr h17 =>
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h18 =>
          -- False on the left can always be used.
          apply False.elim h18
        case inr h19 =>
          -- Conjunctions on the left can always be decomposed.
          let h20 := h19.left
          let h21 := h19.right
          -- Disjunctions on the left can always be decomposed.
          cases h20
          case inl h22 =>
            -- Conjunctions on the left can always be decomposed.
            let h23 := h22.left
            let h24 := h22.right
            -- False on the left can always be used.
            apply False.elim h24
          case inr h25 =>
            -- One of the premise coincides with the conclusion.
            exact h21
    -- We have shown the premise of h11, we can now drive its conclusion.
    let h26 := h11 h14
    -- One of the premise coincides with the conclusion.
    exact h26
  -- We have shown the premise of h12, we can now drive its conclusion.
  let h27 := h12 h13
  -- False on the left can always be used.
  apply False.elim h27
  -- Conjunctions on the left can always be decomposed.
  let h28 := h1.left
  let h29 := h1.right
  -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
  have h30 : p2 := by
    -- We want to use the implication h28 based on <expert-advice>. So we show its premise.
    have h31 : (p1 ∨ (p3 ∨ ((p3 ∨ (False ∨ (((p4 ∧ False) ∨ p5) ∧ p3))) → p3))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h32
      -- Disjunctions on the left can always be decomposed.
      cases h32
      case inl h33 =>
        -- One of the premise coincides with the conclusion.
        exact h33
      case inr h34 =>
        -- Disjunctions on the left can always be decomposed.
        cases h34
        case inl h35 =>
          -- False on the left can always be used.
          apply False.elim h35
        case inr h36 =>
          -- Conjunctions on the left can always be decomposed.
          let h37 := h36.left
          let h38 := h36.right
          -- Disjunctions on the left can always be decomposed.
          cases h37
          case inl h39 =>
            -- Conjunctions on the left can always be decomposed.
            let h40 := h39.left
            let h41 := h39.right
            -- False on the left can always be used.
            apply False.elim h41
          case inr h42 =>
            -- One of the premise coincides with the conclusion.
            exact h38
    -- We have shown the premise of h28, we can now drive its conclusion.
    let h43 := h28 h31
    -- One of the premise coincides with the conclusion.
    exact h43
  -- We have shown the premise of h29, we can now drive its conclusion.
  let h44 := h29 h30
  -- False on the left can always be used.
  apply False.elim h44



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262219914945203964145599806429 : (True ∧ ((((p1 ∨ (((True → (p5 → p4)) ∨ True) → ((False ∨ False) ∧ p1))) ∨ (p4 → ((p4 → (True ∨ p4)) ∨ p4))) ∧ (True → p1)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166256819880016383695582591579 : ((p3 ∧ ((((p4 ∨ p5) → p4) → (((p5 → p3) ∧ p1) ∧ p2)) ∨ ((True ∧ p5) → p4))) ∨ (((True → (False ∨ (False ∧ p2))) ∧ p1) → False)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190692630514478404343978023158 : (((((p3 → p4) → (p3 ∧ p3)) ∧ p2) ∧ (p4 → p1)) ∨ ((((p1 ∧ False) ∨ False) → (((p3 ∧ True) ∧ p5) → (p3 → (False ∨ p4)))) ∨ p3)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244528721575891097385106340659 : ((False ∧ p3) ∨ ((p2 → p2) → (((((True ∧ ((p4 ∨ ((True ∧ p3) ∧ ((p5 ∨ (p5 ∨ True)) → p1))) ∧ p4)) → p5) → p3) ∧ p2) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138774001810410095203833152292 : ((((p1 → p1) ∧ (p5 → (((p2 ∧ ((p3 ∧ (((p5 → p5) ∨ p4) → p2)) ∨ (p5 ∧ p2))) ∧ False) ∨ p1))) ∧ p1) → ((p1 → False) → p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h7 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h7
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313994584378964532841251108410 : (p3 ∨ (((p1 ∧ p1) ∧ (((((False ∧ (True ∨ p1)) ∧ p5) ∨ p4) → p2) → ((True ∧ ((False ∧ (p2 ∧ p5)) → p3)) → p3))) ∨ (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172820804106129628404194094232 : ((True ∧ ((p4 ∧ ((True → p2) → p3)) → (((p5 ∨ p1) ∧ (p3 → p4)) ∧ p1))) ∨ ((p3 ∨ True) → (False → (((p1 ∧ True) ∨ False) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351404572974912147445703634034 : (p4 → ((((p3 ∧ (False → False)) ∧ (p2 ∨ ((p1 → False) ∧ (p4 → p3)))) ∨ (((p2 ∨ p3) ∨ p5) ∨ True)) ∨ ((p2 → True) ∨ (False → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112519955473810792472706529196 : ((((((((True ∨ (((p1 ∨ p4) → False) ∨ (p5 → ((p3 ∧ True) ∧ p4)))) ∧ p5) ∧ p5) ∧ (True → True)) → p1) → p2) → False) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720847698532018930226425259391 : (((((p2 → (p3 → False)) → p5) → (((((True ∨ p2) ∧ p3) ∨ ((p3 ∨ True) ∧ (((p5 ∨ True) → p5) ∧ (False ∧ p5)))) ∨ p2) ∨ True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_136281774984671390353339002795 : ((((True ∧ p3) ∨ (p2 ∧ (p5 → p3))) → ((p1 ∧ (True ∨ p4)) ∨ (((p5 ∧ p2) ∨ (p4 ∨ (p5 ∨ p1))) ∨ p3))) ∨ ((p2 → p2) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199507216509218577373846196107 : (((p2 → ((False ∧ True) ∨ (p3 ∨ p2))) ∨ p3) → ((p1 ∧ p4) → ((False ∨ ((p2 ∨ p2) ∨ (((p3 ∧ p3) ∧ p5) → True))) ∧ (False → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
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
  -- Implications on the right can always be decomposed.
  intro h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_646456795484598322978145311038 : ((((p1 → (((p5 → ((p5 ∨ (True → (True ∧ (((False → (p2 → (False ∧ p2))) ∨ p4) → p5)))) ∨ (p1 ∧ p2))) → p4) → p2)) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141749507272883859818244130028 : (((p1 → p1) ∧ (((p2 ∨ (p5 → False)) ∧ ((p2 → (p3 → (p5 ∨ p3))) → ((p5 ∧ p1) ∧ (True → p5)))) ∧ True)) → (True ∧ (p2 → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h10 : (p2 → (p3 → (p5 ∨ p3))) := by
      -- Implications on the right can always be decomposed.
      intro h11
      -- Implications on the right can always be decomposed.
      intro h12
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h12
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h13 := h8 h10
    -- We need to get the left conjuct of h13 based on <expert-advice>.
    let h14 := h13.left
    -- We need to get the right conjuct of h14 based on <expert-advice>.
    let h15 := h14.right
    -- One of the premise coincides with the conclusion.
    exact h15
  case inr h16 =>
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h17 : (p2 → (p3 → (p5 ∨ p3))) := by
      -- Implications on the right can always be decomposed.
      intro h18
      -- Implications on the right can always be decomposed.
      intro h19
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h19
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h20 := h8 h17
    -- We need to get the left conjuct of h20 based on <expert-advice>.
    let h21 := h20.left
    -- We need to get the right conjuct of h21 based on <expert-advice>.
    let h22 := h21.right
    -- One of the premise coincides with the conclusion.
    exact h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149219983315165092781165334079 : (((p2 ∧ p2) ∨ ((False ∨ ((((p3 ∨ p4) → False) ∨ (False → (p5 ∧ p5))) ∧ (p5 ∨ (False ∧ p1)))) → p2)) ∨ ((False ∧ p5) → (p5 ∧ p4))) := by
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
theorem thm_5_vars_688040784534672584326952146856 : (((((p2 ∨ (((p4 ∨ p5) → p2) ∧ p5)) → ((True → (p2 ∧ p2)) ∧ (False → False))) ∧ ((p2 → (p2 ∧ True)) → ((True ∧ p2) ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190727461240276762904749005712 : ((((p5 ∨ p2) ∧ ((p5 ∧ p5) ∧ p2)) ∧ (p3 ∨ p5)) ∨ (((False ∧ p3) ∨ (p3 ∨ (p5 ∨ (p4 ∨ (False ∨ (p1 → p2)))))) → (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_188903703663940361324922829079 : ((((p1 ∨ p3) ∧ (True ∧ p1)) → ((True ∧ p1) ∨ p3)) ∧ ((((True ∨ p2) → ((p3 ∧ p3) → p2)) → ((p1 ∨ p4) ∧ (p1 → True))) ∨ True)) := by
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
    let h5 := h3.left
    let h6 := h3.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h3.left
    let h9 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166434761420080044503193712088 : ((p1 ∨ (p5 ∨ (((True ∨ ((p1 ∧ ((p2 → False) ∧ True)) → True)) → False) ∨ (p1 → p3)))) ∨ (p1 → (p1 ∧ ((p5 → (False ∨ p1)) ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_18888083839270646765642283056 : ((((p2 ∧ p4) ∧ (p2 ∧ (p3 ∧ (p5 ∧ (p2 → (p5 ∧ ((False ∧ (p3 ∧ True)) ∧ False))))))) ∨ (True ∨ ((p1 ∨ (p1 ∧ p5)) ∧ p4))) ∧ True) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_19668172464623251444085638827 : (((p2 ∨ (p2 ∧ ((((True ∧ p1) ∨ ((p4 → p2) ∨ (p5 ∨ False))) → p5) → p4))) ∨ ((False → (p2 ∨ (p1 ∧ p5))) ∧ (p5 → True))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_641273145376563120771183713845 : (((((True → True) ∨ (p4 → (p3 ∧ ((((True ∧ p3) ∧ (p2 → ((True ∨ True) → ((p1 → p5) ∧ False)))) → p5) ∧ (p4 ∨ p3))))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126690606701813926737030035173 : ((p4 ∧ (((p2 → p1) ∨ ((p4 → (((((True → (p3 → p1)) ∧ p5) → p2) ∨ ((p4 → p4) → True)) ∧ p3)) → p3)) → p1)) → (p1 ∨ True)) := by
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
theorem thm_5_vars_58685508791186458363176563695 : (((p2 → p1) ∧ (p3 ∨ (((p1 ∨ True) → p5) ∧ (p3 ∧ (p1 ∧ ((p1 ∧ (((p5 ∧ p5) ∨ p2) ∧ (p4 ∧ (p2 → p2)))) → p3)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337658583645547729256032583767 : (p1 → (((p3 ∧ (p4 ∨ (((p1 ∧ (False ∨ p3)) ∧ ((p3 → True) ∨ p3)) → p5))) ∨ (p3 ∧ p2)) ∨ (p5 → (p2 ∨ (p4 ∨ (p5 ∧ True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135712102487133447196093904535 : (((p4 ∧ ((((p1 ∧ p2) → (p2 → (True → (False ∧ p2)))) ∨ p4) ∨ False)) ∧ (((p1 ∧ True) → (p2 ∨ p3)) ∨ p5)) ∨ (True → (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



