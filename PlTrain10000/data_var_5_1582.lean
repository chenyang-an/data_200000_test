variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601145576350114041707272473662 : ((((p1 ∧ (p3 → ((p5 ∧ (p5 ∧ ((p1 ∨ True) ∨ ((False ∨ (((p4 ∧ p3) → False) → p5)) → (p3 ∧ (p5 → True)))))) → False))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355526197249662176613187633516 : (p5 → ((((((p5 ∧ (((((p3 ∨ True) ∨ p2) ∨ p5) → False) ∧ (True ∨ (p3 ∨ (p4 ∨ p1))))) ∨ False) → p3) ∧ p1) ∧ p4) ∨ (p5 ∧ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193558416561544276811918581430 : (((True ∨ True) → (False ∧ ((p5 → p2) ∧ (p4 ∨ True)))) → ((p1 ∨ p1) ∨ ((p4 ∨ (p2 ∧ ((((p3 ∨ p5) → p2) → p5) ∨ True))) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ True) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54953895547922608580499302041 : (((((p3 ∧ p3) ∨ p1) ∨ (p2 ∧ p1)) ∧ (((True ∨ p1) ∨ p1) → (((False → p1) → ((p5 ∧ (False ∧ True)) → True)) → (p3 → p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328792945331357516169533494216 : (True → (((p3 ∧ ((p3 ∨ p1) → False)) ∧ (p5 ∧ (p4 ∧ p4))) ∨ (True ∨ (True ∨ (((p5 ∨ p3) ∧ p4) ∨ ((p5 → p3) → (p5 → p3))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204651465205506289121755659101 : (((p3 ∧ ((p5 ∨ p3) ∨ p4)) ∨ p1) ∨ (True ∨ ((p2 ∨ ((True ∨ p1) ∧ (((p2 → p3) → False) → (p2 ∧ ((p1 ∨ p1) ∨ False))))) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164840167875287436783683439721 : (((p2 ∧ (p4 ∧ ((((((p3 → p5) → p1) → False) ∨ (p5 ∨ True)) → p1) → False))) ∨ False) ∨ (True ∧ (p3 → (((p2 ∧ p2) ∨ p2) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135690691779238502767235439031 : ((((False → (False → (p3 ∨ ((p3 → (True ∨ (p3 → p4))) → p3)))) → p2) ∧ ((p5 ∧ True) ∧ ((p3 ∨ p4) ∨ p1))) ∨ (True ∧ (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47723367892567476118929999093 : (((((False ∧ ((((((p4 ∨ False) → True) ∧ (p1 ∨ p4)) ∨ (False ∨ ((p3 → p2) → p3))) ∨ p4) ∨ False)) → True) ∨ p3) → (False ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206475498962236219786780576265 : ((p5 ∨ (((p2 ∨ p3) ∧ True) ∧ p2)) ∨ ((((True → False) → (p1 ∨ (p4 ∧ True))) ∨ ((p3 ∨ (True ∧ (False → p2))) ∨ p2)) ∧ (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262518119511449485302251820523 : (True ∧ ((p5 → (((False → ((p3 → True) ∨ (p4 → (p4 ∧ (p4 ∨ (((True ∧ False) → p5) ∨ (p2 → p1))))))) ∨ p4) → (p1 ∧ p3))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119095707584376298643642678908 : ((p1 → ((p2 ∧ ((p2 ∨ (p4 ∨ p5)) ∧ (p5 → p2))) → ((p1 → (((p3 → p2) → p2) → ((True → p4) ∧ False))) → p3))) ∨ (p1 ∧ p3)) := by
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
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h9 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h10 := h3 h9
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h11 : ((p3 → p2) → p2) := by
      -- Implications on the right can always be decomposed.
      intro h12
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h13 := h10 h11
    -- We need to get the right conjuct of h13 based on <expert-advice>.
    let h14 := h13.right
    -- False on the left can always be used.
    apply False.elim h14
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h17 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h1
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h18 := h3 h17
      -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
      have h19 : ((p3 → p2) → p2) := by
        -- Implications on the right can always be decomposed.
        intro h20
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h18, we can now drive its conclusion.
      let h21 := h18 h19
      -- We need to get the right conjuct of h21 based on <expert-advice>.
      let h22 := h21.right
      -- False on the left can always be used.
      apply False.elim h22
    case inr h23 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h24 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h1
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h25 := h3 h24
      -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
      have h26 : ((p3 → p2) → p2) := by
        -- Implications on the right can always be decomposed.
        intro h27
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h25, we can now drive its conclusion.
      let h28 := h25 h26
      -- We need to get the right conjuct of h28 based on <expert-advice>.
      let h29 := h28.right
      -- False on the left can always be used.
      apply False.elim h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249534494740998356843338465752 : ((p5 ∨ p2) ∨ ((((p2 ∨ (p5 → True)) ∨ False) ∧ (((p4 ∨ p4) → (False ∨ ((p3 → (False → p2)) ∧ (False ∨ True)))) ∨ (p1 → p3))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43953022114700411567423165226 : (((((p5 ∧ p3) ∨ (((((p1 ∨ ((False ∨ p3) ∧ p5)) ∨ False) → False) ∨ (p3 ∧ (p4 → (True → True)))) ∧ p2)) ∨ (p2 → p1)) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346285777964876511708347021488 : (p3 → ((((p1 ∨ (p4 ∧ ((p4 ∨ True) ∨ p5))) ∧ ((p5 → ((((p5 → True) → (p2 → p1)) → True) ∧ p3)) → p4)) ∧ p1) ∨ (p4 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245694433006250629770558072695 : ((p3 ∧ p1) ∨ (True → (((((((p4 ∨ p5) → (False ∨ True)) → ((p3 ∨ True) → p3)) ∨ p1) ∧ p2) ∨ True) ∨ (p5 ∧ ((p4 ∨ p3) ∧ True))))) := by
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
theorem thm_5_vars_180225258631885801922246938350 : (((True ∧ (((p4 ∧ p3) ∨ False) ∨ (p2 → (p5 ∨ (p2 → p1))))) → p5) → (((p2 ∨ ((p1 → p5) ∨ p4)) ∨ p5) ∧ (p5 ∨ (True ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (True ∧ (((p4 ∧ p3) ∨ False) ∨ (p2 → (p5 ∨ (p2 → p1))))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47237712499293201801569161536 : ((((((p4 → ((True → False) ∨ True)) ∧ False) → False) → ((p2 ∧ (True → False)) ∨ (((p2 ∧ (p5 ∧ p5)) ∨ p2) ∨ p3))) ∨ (p3 ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134324137464839938708716335841 : (((p2 ∧ ((p3 ∨ ((False ∨ (p3 → (((p4 ∨ False) ∨ False) → (True → ((p2 ∧ False) → p3))))) ∧ p1)) ∧ p5)) ∨ True) ∨ ((p4 ∨ p4) ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_222221309483807603150331609482 : (((True → False) → True) ∧ ((((p3 ∧ ((False ∧ p4) ∧ (p4 ∧ True))) ∨ ((p2 ∨ p5) ∧ True)) ∧ p2) ∨ ((False ∨ (p2 → (p2 ∨ p3))) ∨ p1))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142274753538719843653743701850 : ((p2 ∧ ((p2 ∧ ((p2 → (True ∨ p2)) → p2)) ∨ ((True ∨ p1) ∨ (False ∧ (p1 ∧ ((p2 ∧ (p3 ∧ p1)) ∨ p3)))))) → (p5 ∨ (False ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- False on the left can always be used.
      apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147605519903209624531644867040 : (((((p1 → (p1 ∨ False)) → (((p5 ∧ p3) ∨ (p3 ∨ (((False → p2) ∨ p3) ∧ p5))) ∧ p3)) ∨ p2) → p5) ∨ (((p3 ∧ False) ∧ True) → p3)) := by
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
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684552932889816463525122307685 : (((((p1 ∨ ((True ∨ False) ∧ p5)) ∧ (True ∧ (p3 ∨ ((((p5 ∨ p3) ∨ p1) → False) ∧ p5)))) ∨ (False → (p4 → ((p5 → False) → p5)))) ∨ False) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158301196748903991344207778954 : ((((p4 ∨ p1) → p1) → (p3 → (p2 ∨ ((((True → (p2 ∧ (False ∧ p4))) ∨ p4) → p4) ∧ p4)))) ∨ ((False ∨ p1) ∨ (p2 → (True → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193399250024974691861403067782 : (((p3 ∧ p5) ∧ (p4 ∧ ((p4 ∨ p3) ∨ (p2 ∧ p5)))) → (((((False → p4) → p5) → True) ∧ (True → ((p4 ∧ (False ∧ False)) ∧ p2))) → p2)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h9 := h6.left
  let h10 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h13 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h14 := h4 h13
      -- We need to get the left conjuct of h14 based on <expert-advice>.
      let h15 := h14.left
      -- We need to get the right conjuct of h15 based on <expert-advice>.
      let h16 := h15.right
      -- We need to get the left conjuct of h16 based on <expert-advice>.
      let h17 := h16.left
      -- False on the left can always be used.
      apply False.elim h17
    case inr h18 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h19 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h20 := h4 h19
      -- We need to get the left conjuct of h20 based on <expert-advice>.
      let h21 := h20.left
      -- We need to get the right conjuct of h21 based on <expert-advice>.
      let h22 := h21.right
      -- We need to get the left conjuct of h22 based on <expert-advice>.
      let h23 := h22.left
      -- False on the left can always be used.
      apply False.elim h23
  case inr h24 =>
    -- Conjunctions on the left can always be decomposed.
    let h25 := h24.left
    let h26 := h24.right
    -- One of the premise coincides with the conclusion.
    exact h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299943810539451496083969549139 : (False ∨ ((((((p3 ∨ ((((p3 → p3) ∧ (p2 ∧ (p4 → p2))) ∧ p3) ∧ p3)) → p3) → ((True ∧ p3) ∨ p5)) ∨ p1) ∨ True) ∧ (p4 → p4))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40093835415900929461484193760 : (((((p5 ∧ ((p5 ∨ ((p1 ∨ p1) → True)) → ((p3 ∨ (p2 ∨ True)) → ((p5 → (p1 ∧ (p4 → p3))) ∨ True)))) → False) ∧ p2) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113964245061218755846474672715 : (((True ∧ (((False ∧ p2) ∨ ((p4 ∧ (p3 → False)) → (True ∨ False))) → (False ∨ ((p5 ∨ p3) ∧ p1)))) ∧ ((p3 ∧ p2) ∨ True)) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149835361604832704123682850601 : ((p1 ∨ (((p4 → p3) → ((p1 → (p3 → p4)) ∨ p5)) ∨ ((p4 ∨ (p3 ∧ (p2 ∨ (p3 ∧ True)))) → p3))) ∨ (False → ((p2 → True) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168885383253459631615176085304 : ((p4 ∨ (p2 ∨ ((True ∨ (p1 ∨ ((True ∨ ((p2 → p2) → (p4 → p2))) ∧ True))) ∧ p2))) → (((p5 ∧ (p5 ∨ p4)) ∨ (p1 ∨ False)) ∨ True)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
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
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h11 =>
          -- Conjunctions on the left can always be decomposed.
          let h12 := h11.left
          let h13 := h11.right
          -- Disjunctions on the left can always be decomposed.
          cases h12
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
theorem thm_5_vars_965987461489593393291216615945 : ((((p5 ∧ False) ∨ ((True ∧ (((p5 → p1) ∧ p1) ∧ (((True ∨ True) → p1) ∨ (p1 ∨ ((False ∨ p2) ∨ True))))) ∧ ((p4 → p5) → p1))) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h14 =>
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- One of the premise coincides with the conclusion.
        exact h16
      case inr h17 =>
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h18 =>
          -- Disjunctions on the left can always be decomposed.
          cases h18
          case inl h19 =>
            -- False on the left can always be used.
            apply False.elim h19
          case inr h20 =>
            -- One of the premise coincides with the conclusion.
            exact h13
        case inr h21 =>
          -- One of the premise coincides with the conclusion.
          exact h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185373391729612814013520646761 : ((p5 ∧ ((((p3 ∧ p5) ∨ p5) ∧ (p5 ∨ (p1 → p5))) → p4)) ∨ (p1 ∨ ((False ∨ p1) → (False ∨ ((p2 ∨ p4) → (p2 → (p1 ∨ p5))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311898820304857147668250527002 : (p2 ∨ (p2 ∨ ((p5 ∨ False) ∨ ((True ∧ (((p5 → (p4 ∧ p5)) ∨ ((((True ∧ p2) ∧ True) → ((p4 → p2) ∨ p2)) ∨ p5)) → p2)) ∨ True)))) := by
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
theorem thm_5_vars_56840753638782911975199947001 : ((((p5 → p1) → p4) ∧ ((p2 ∨ (True ∨ p4)) → ((p4 ∧ p2) ∧ ((p4 ∧ (False ∧ p2)) ∨ ((p3 → ((p3 ∧ p4) → True)) ∧ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115392878875135978974238196368 : ((((p4 → p3) → (((True ∨ p2) → p5) → p5)) ∧ ((p2 → ((p4 → (p2 ∨ (True ∧ (p3 ∨ p5)))) ∧ (p1 ∨ p4))) ∧ True)) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172115179380206764923526778835 : ((((p1 → ((((True ∨ p5) → True) → p5) ∧ p2)) ∧ p1) ∧ (True ∨ (p3 → p5))) ∨ (p3 → ((p2 → p4) → (((p5 ∨ p3) ∨ False) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116476415942024706369371603812 : (((p1 ∧ p2) ∧ ((p4 ∧ (((p3 ∧ True) ∨ ((True ∨ (p4 ∨ p1)) → p1)) ∧ (p4 → False))) ∨ (((p3 ∧ p4) → p5) ∧ False))) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325779069798743032928790690786 : (p5 ∨ (p2 ∨ (p3 ∨ (((p1 ∨ (((p5 ∧ p4) ∨ p5) → (((True → True) ∨ False) ∧ p3))) ∨ (((False ∨ p5) ∨ p1) → (False → p1))) ∨ p2)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156876777716234290321463859304 : ((((p1 → ((p4 → ((p3 ∧ p5) → p5)) → (((p5 ∧ p1) → (p5 ∧ p4)) → False))) ∧ p3) ∨ p4) ∨ ((True ∨ (p3 ∨ (p1 ∧ p2))) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147073041035872606821965760604 : (((((p2 ∨ ((p4 ∧ True) ∨ p4)) ∧ p3) ∨ ((True → (p1 ∧ (p1 ∨ (p3 ∨ False)))) ∧ (p4 → p3))) ∧ p3) ∨ (((p1 → p4) ∨ True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116425158181152700853826663797 : (((p5 ∨ (True ∨ p2)) → ((p4 → ((((p2 ∧ p1) ∨ (p1 ∨ ((p2 → (p5 ∨ (p4 ∨ True))) → p5))) ∨ p1) ∨ False)) ∧ False)) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191259721314663855173418556502 : (((p4 ∧ p4) ∧ (((False ∨ p4) ∨ (p1 → p4)) ∧ p1)) ∨ (True ∨ (p3 ∨ (p4 ∧ (((p1 → (True ∧ (p2 ∧ p2))) → p3) ∧ (p2 → p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156939978746327754625790778811 : (((((p5 → (((p4 ∧ p5) → p1) ∧ p2)) → (p3 ∧ (False ∨ (p4 ∨ p4)))) ∨ (True → p5)) ∨ p5) ∨ (p4 ∨ ((True ∨ (True ∧ p5)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336963220273508944916280654860 : (p1 → (((p3 ∨ (((p2 ∧ p1) ∨ (p5 → (False ∧ (p1 ∨ (p3 → p2))))) ∨ (p1 → (p2 ∨ True)))) → (False ∨ (p2 → True))) ∧ (p2 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h12
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- True on the right can always be proven directly.
      apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135059840420832795891984153049 : (((((False → (p3 ∨ ((p4 ∨ (True → (p1 ∧ True))) ∧ p4))) ∧ ((p5 ∨ p3) ∧ (p5 → p4))) → p5) ∨ (p3 ∨ True)) ∨ (p2 → (p5 ∨ p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231640447641126108061642121492 : (((False ∧ p2) → True) → (p3 → (((p5 ∨ (((p4 → ((p5 ∧ (p2 ∧ True)) ∨ (p5 ∨ p2))) ∨ p5) ∧ p4)) ∧ (p4 ∨ (True ∧ p2))) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219895568258752205536131479724 : ((p4 → ((p2 ∨ p5) ∨ p2)) → ((p4 → p1) ∨ ((True → p4) ∨ ((p5 ∨ p3) → (p1 ∨ (True ∧ ((True ∨ p1) ∨ ((p5 ∨ p4) → p1)))))))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
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
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47102762662966647363771422581 : (((((((p5 → (p4 → (False ∨ p3))) → p4) → False) → (((p1 → p1) ∧ p1) ∧ (False ∧ False))) ∧ (False → (True ∨ p2))) ∨ (p2 ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258327611227344992542850091894 : ((p5 ∨ True) → (p1 → ((p1 ∧ (p4 ∨ (((p5 ∧ True) → p5) → (p4 ∧ ((p5 ∨ p3) ∧ (((False → (p1 ∨ True)) ∨ True) ∨ p2)))))) ∨ p1))) := by
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
theorem thm_5_vars_58143566813416623187623144891 : (((p2 ∧ p3) ∧ ((((((False ∧ p5) ∧ p5) → (p2 ∨ True)) → p3) ∨ p5) ∨ (p4 → (((p2 ∨ ((True ∧ False) ∨ p1)) ∨ p4) ∧ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171665565738937042496002349846 : (((p4 ∧ (((p5 ∨ (False ∨ (p5 ∧ p2))) ∨ p1) ∧ ((p5 ∨ False) → p4))) ∨ p5) ∨ ((((p1 ∧ p5) ∨ False) → (p1 → (True ∨ p2))) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66003141748597487407106990066 : ((p4 ∨ (p5 → (((True ∧ p4) ∨ (p2 ∨ (p4 → ((p4 → (p3 ∧ True)) ∧ (p4 ∨ (p3 ∨ p3)))))) ∨ ((p1 ∨ True) → (True → p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_691853183823633475966320866462 : ((((True → (True → (((False ∧ p2) ∨ p4) ∨ (((False ∧ (False ∧ True)) → p4) → p2)))) → (p1 ∨ (False ∨ (p1 → (p5 ∧ (p4 → p5)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693852473315064862518733915258 : ((((((p2 ∨ p1) → (p3 ∨ (p3 ∨ ((p1 → True) ∧ (p5 ∧ True))))) → p5) ∨ (True ∨ (False ∧ (p2 → (p3 → ((p5 ∨ p1) → p3)))))) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_172777977218807515389611804883 : (((p4 ∨ False) → (((False → True) → (((p2 ∨ p3) ∧ p3) ∧ (p3 ∧ p4))) ∨ p2)) ∨ (False → (p4 ∧ ((p3 → (p4 → False)) ∧ (False → p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164690268423169787467842781304 : ((((((p3 → (p2 ∨ ((p1 ∧ ((p1 ∧ True) ∧ p1)) ∧ p4))) ∧ p2) ∧ p1) ∨ True) ∨ True) ∨ ((((p2 ∧ p1) ∨ p3) ∨ p1) ∨ (p5 ∨ True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_719980105060933328321522506407 : ((((((p2 ∨ p2) ∧ p1) ∧ p2) → ((p2 → ((p1 → (True → p1)) → (((((p1 ∧ p4) ∨ p5) ∨ True) → (False ∨ p2)) ∨ True))) ∨ p4)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152645762808038601896675039913 : (((True → False) ∧ (((((False ∨ (p1 ∨ False)) ∧ (False → (((p3 ∧ p4) ∨ p1) ∨ p1))) ∧ p2) ∨ p1) ∧ p2)) → (p3 ∨ ((p5 ∧ True) ∧ p4))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h14 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h15 := h2 h14
        -- False on the left can always be used.
        apply False.elim h15
      case inr h16 =>
        -- False on the left can always be used.
        apply False.elim h16
  case inr h17 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h18 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h19 := h2 h18
    -- False on the left can always be used.
    apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40057899721656190198574011815 : ((((((p5 ∨ (p5 → (p5 ∨ (((((p4 ∧ True) → False) ∨ True) → (True ∨ True)) ∧ False)))) → ((p1 ∨ p4) → p1)) ∨ p2) ∧ p1) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49692677272257548021125822875 : ((((p3 ∨ p1) ∨ ((True → (False → p2)) ∨ (True ∨ (((p4 → p2) ∨ True) ∧ (False ∨ (p2 ∧ (False → p1))))))) → (p3 ∧ (p3 → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57301853701167416494058761046 : ((((p4 → p5) → p1) ∨ ((p5 → p4) ∨ ((p4 ∧ (p5 → ((p4 → False) → (p4 → (((p4 → p1) → False) ∧ True))))) → (p5 → p5)))) ∨ p1) := by
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
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680282364536969303688245065469 : ((((((((((p1 ∧ p5) → p1) ∧ p3) → (p3 ∨ p5)) → (False ∨ p5)) ∨ p1) ∧ (p4 ∨ (False → p4))) → (p3 ∧ ((p3 → True) ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_773243458162077509935263239360 : (((False ∨ (((p3 ∨ ((p2 ∨ (p5 ∨ (p3 → p3))) ∧ ((p5 ∨ ((p5 ∨ True) ∨ p4)) ∨ p2))) ∧ ((p3 → True) ∨ (p5 → p3))) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60450944070180124489929915588 : (((p5 → False) → (False ∨ (((p2 → p2) ∧ False) ∨ (False ∧ (p2 ∨ ((True ∨ ((True ∨ p3) ∧ (True → ((True ∧ False) ∨ p3)))) ∧ p2)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309909156321547336696480072521 : (p2 ∨ (((((p1 ∨ p1) → (((True → False) ∨ (p1 ∨ True)) → p4)) → ((p1 → True) → p2)) ∧ True) ∨ (p5 → ((p2 ∨ True) ∨ (False ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_258192547535183126775297659503 : ((p4 ∨ p4) → ((p4 ∨ p4) → (((((((p5 ∧ (True → False)) ∧ p2) ∨ p3) ∨ (True ∧ (p3 ∧ True))) ∧ True) → ((False ∧ p4) ∨ p4)) ∨ False))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h5
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Conjunctions on the left can always be decomposed.
          let h10 := h9.left
          let h11 := h9.right
          -- Conjunctions on the left can always be decomposed.
          let h12 := h10.left
          let h13 := h10.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h4
        case inr h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h4
      case inr h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h15.left
        let h17 := h15.right
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
    case inr h20 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h21
      -- Conjunctions on the left can always be decomposed.
      let h22 := h21.left
      let h23 := h21.right
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h24 =>
        -- Disjunctions on the left can always be decomposed.
        cases h24
        case inl h25 =>
          -- Conjunctions on the left can always be decomposed.
          let h26 := h25.left
          let h27 := h25.right
          -- Conjunctions on the left can always be decomposed.
          let h28 := h26.left
          let h29 := h26.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h20
        case inr h30 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h20
      case inr h31 =>
        -- Conjunctions on the left can always be decomposed.
        let h32 := h31.left
        let h33 := h31.right
        -- Conjunctions on the left can always be decomposed.
        let h34 := h33.left
        let h35 := h33.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h20
  case inr h36 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h37 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h38
      -- Conjunctions on the left can always be decomposed.
      let h39 := h38.left
      let h40 := h38.right
      -- Disjunctions on the left can always be decomposed.
      cases h39
      case inl h41 =>
        -- Disjunctions on the left can always be decomposed.
        cases h41
        case inl h42 =>
          -- Conjunctions on the left can always be decomposed.
          let h43 := h42.left
          let h44 := h42.right
          -- Conjunctions on the left can always be decomposed.
          let h45 := h43.left
          let h46 := h43.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h37
        case inr h47 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h37
      case inr h48 =>
        -- Conjunctions on the left can always be decomposed.
        let h49 := h48.left
        let h50 := h48.right
        -- Conjunctions on the left can always be decomposed.
        let h51 := h50.left
        let h52 := h50.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h37
    case inr h53 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h54
      -- Conjunctions on the left can always be decomposed.
      let h55 := h54.left
      let h56 := h54.right
      -- Disjunctions on the left can always be decomposed.
      cases h55
      case inl h57 =>
        -- Disjunctions on the left can always be decomposed.
        cases h57
        case inl h58 =>
          -- Conjunctions on the left can always be decomposed.
          let h59 := h58.left
          let h60 := h58.right
          -- Conjunctions on the left can always be decomposed.
          let h61 := h59.left
          let h62 := h59.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h53
        case inr h63 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h53
      case inr h64 =>
        -- Conjunctions on the left can always be decomposed.
        let h65 := h64.left
        let h66 := h64.right
        -- Conjunctions on the left can always be decomposed.
        let h67 := h66.left
        let h68 := h66.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h53



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_652132894278856760487599163534 : ((((p1 ∧ (((p1 → ((True ∨ (p5 ∨ p3)) ∨ True)) ∧ (False ∧ p1)) ∧ ((p5 ∨ p3) ∨ (((p3 → True) → p1) ∨ True)))) ∧ (p4 ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158967052745311603353664491785 : ((p3 ∨ ((((p1 ∨ p2) ∧ p5) → ((p1 ∧ False) ∧ ((((p1 → p3) ∨ True) ∨ p5) → p4))) ∧ True)) ∨ (p4 ∨ ((p5 → p5) ∨ (p5 → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112500803120298754125804464583 : ((((p3 → ((p2 ∧ (p2 ∧ (p5 → True))) ∧ (((((p3 ∧ (p4 ∨ p1)) → (p1 → p1)) ∧ p3) ∨ p1) → p3))) ∨ p4) → p5) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232964449931682871204649655855 : ((p3 ∧ (True → p3)) → (((p5 → p1) → (((((p3 ∧ (p2 → ((p4 → p2) ∧ (p1 → True)))) ∧ (p1 ∧ p3)) ∨ p4) → p2) ∨ p1)) ∨ p3)) := by
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
theorem thm_5_vars_350252774090477179091385800809 : (p4 → ((False ∧ (p4 → ((((p5 → (((p5 → (p4 ∧ p4)) ∧ p3) ∨ p3)) → ((True ∨ (p4 ∨ p4)) ∧ p2)) ∨ False) ∧ (False ∧ p4)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621029955764370726201335366638 : (((((False → p5) → (p4 ∧ ((((p3 → (p1 → ((p3 → p5) ∧ (p1 ∨ (p5 ∧ p1))))) ∨ p1) → p1) ∨ (True ∧ (False → p4))))) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_720316287839235338046486900475 : ((((((p1 ∧ False) ∨ p4) ∨ False) → (p5 ∨ (((((p1 → p2) → (p1 ∨ (p3 → p1))) ∧ (p5 ∧ p4)) → p2) → (False ∨ (True → False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320318361494447946968055196641 : (p4 ∨ ((p2 ∨ p1) ∨ (p3 → (((False ∨ (((True ∨ False) → False) → (((p3 ∧ (p2 ∧ p3)) ∨ p3) ∧ True))) ∨ p1) ∨ (p3 ∧ (p2 ∨ False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165742925541628013750110591503 : ((((True → (False → True)) → p4) ∨ (((p1 ∧ ((p4 ∨ (p2 → False)) ∨ p2)) ∨ p2) ∨ p2)) ∨ ((p4 ∧ (p3 ∧ ((p4 → p5) ∧ p1))) → p4)) := by
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
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173078926430098813811704825127 : ((p1 ∨ (((((p2 ∨ False) ∧ True) ∧ p1) ∧ (p1 → (p5 ∧ (p5 → p2)))) ∨ True)) ∨ (((True ∧ p1) ∧ (p3 ∧ ((True ∨ p2) ∨ False))) ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670610065494391506342930587397 : (((((p5 → p2) ∨ (p1 ∨ (((((True ∧ (False → (p3 → p4))) ∨ p2) ∨ (False ∨ p2)) ∨ (p4 ∧ False)) → p1))) ∨ ((p5 → p5) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136439125395200226587278008955 : ((((False ∧ False) → (p1 → True)) → (((((p5 ∧ False) → p2) → (p5 → (p3 → False))) ∧ (p4 ∧ p5)) → (p2 ∧ p5))) ∨ (True → (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42243124693182634136482888370 : (((False ∧ (False ∨ (p1 ∧ ((((p3 ∨ ((p4 → ((True ∨ (p4 ∧ p4)) ∨ p1)) → p3)) ∨ (p5 ∨ (p3 → False))) ∨ p3) ∨ p3)))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_84531087473698248617886873399 : (((((p4 ∨ p3) ∧ ((p1 ∨ True) ∧ (p3 → p4))) → ((p4 → (False ∨ p2)) ∨ p4)) → (False ∨ ((((False ∧ True) → p3) ∧ p4) ∧ False))) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p4 ∨ p3) ∧ ((p1 ∨ True) ∧ (p3 → p4))) → ((p4 → (False ∨ p2)) ∨ p4)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h5.left
      let h8 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h5.left
      let h13 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h14 =>
        -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
        have h15 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h11
        -- We have shown the premise of h13, we can now drive its conclusion.
        let h16 := h13 h15
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h16
      case inr h17 =>
        -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
        have h18 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h11
        -- We have shown the premise of h13, we can now drive its conclusion.
        let h19 := h13 h18
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h19
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h20 := h1 h2
  -- Disjunctions on the left can always be decomposed.
  cases h20
  case inl h21 =>
    -- False on the left can always be used.
    apply False.elim h21
  case inr h22 =>
    -- Conjunctions on the left can always be decomposed.
    let h23 := h22.left
    let h24 := h22.right
    -- Conjunctions on the left can always be decomposed.
    let h25 := h23.left
    let h26 := h23.right
    -- False on the left can always be used.
    apply False.elim h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171474005292428195991521722209 : (((p3 ∨ ((p5 ∧ (p4 ∧ True)) ∨ (p4 → ((p5 ∨ (p5 ∧ p2)) ∧ True)))) ∧ p3) ∨ ((False ∨ (False → (p1 ∧ p1))) ∨ ((p3 ∧ p2) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_62183247891090159700893732888 : ((p3 ∧ (((p2 ∧ (p5 ∨ (((p4 → (True ∨ ((p4 → True) → p5))) ∧ (p3 ∨ (((p3 → p2) ∧ False) → p5))) ∧ p5))) ∧ p2) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204146351314290147900239809621 : (((((p2 ∧ p1) ∧ p5) ∨ p4) ∧ p3) ∨ (True ∨ ((p3 ∧ p4) ∨ ((p3 → p4) ∨ ((False → (p5 ∨ (True ∨ p4))) ∨ ((p5 ∨ p5) → p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_431099384175664440980217355189 : (((((True ∨ p1) → (((False ∨ p3) ∧ (p2 ∨ (p4 ∨ (((p4 → (p3 → True)) ∧ (True ∧ True)) ∧ False)))) ∨ (True ∧ True))) ∨ (True ∧ True)) ∧ True) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250809144935095846357470156063 : ((p1 → p2) ∨ (((p3 → (False ∨ (((((p4 ∨ False) ∨ False) → (p1 ∨ p3)) ∨ p1) → p4))) ∧ (((p4 → (p3 ∧ p1)) → p5) → p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309609595765915374137875715787 : (p2 ∨ (((p5 ∨ ((p1 ∧ ((p2 → p3) ∨ ((True ∧ (p2 ∧ ((False ∧ p4) ∨ p2))) → (p2 → p4)))) ∧ p5)) ∨ p3) ∨ (True ∨ (p4 → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249655122985812465037557023323 : ((p5 ∨ p4) ∨ (((((False ∧ (False ∨ ((((p4 ∧ p4) ∧ True) ∨ p1) ∧ (p4 ∨ p1)))) → True) → p4) ∨ ((p2 ∧ (p5 ∧ p2)) ∨ True)) ∨ p5)) := by
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
theorem thm_5_vars_179466188372396877254653520552 : ((p5 ∨ (p2 → (p5 ∧ ((p3 ∨ ((p1 ∧ (True → p3)) ∧ p2)) ∧ p1)))) ∨ ((p4 ∧ (p3 ∧ False)) → (((True ∨ p4) → (p5 ∧ True)) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_84029496390655415344443242401 : ((((True ∧ (p4 → ((True → (p3 → (((p4 ∧ p3) ∧ False) → True))) ∨ p5))) → p3) ∧ (False → (((p1 ∧ p2) → (True ∨ p3)) → True))) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (True ∧ (p4 → ((True → (p3 → (((p4 ∧ p3) ∧ False) → True))) ∨ p5))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_688860200709987831258809850754 : (((((((((p5 → (p1 → True)) ∨ p2) ∧ (False ∧ p5)) ∨ True) ∨ (False ∨ p1)) ∧ p3) ∨ ((p5 → p5) ∧ (p5 → ((p1 ∧ False) ∨ True)))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158793857996304236356308839563 : ((p5 ∧ ((False → (((p4 ∧ (True ∨ p2)) ∧ (True ∨ (p5 ∨ p3))) ∧ p1)) → ((p1 ∧ True) → p4))) ∨ ((p3 ∨ (True ∨ (p2 ∨ False))) ∨ p3)) := by
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
theorem thm_5_vars_165451413087640704530951449477 : (((((p4 → False) ∧ (((p4 ∨ p4) ∨ p3) ∧ p4)) → p3) ∧ (p3 ∧ ((True → p3) ∨ p4))) ∨ (True ∨ (p1 → (((p5 → p4) ∧ False) → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254331327957221753595463351049 : ((p2 ∧ p4) → ((((((p2 → False) ∧ p5) ∨ p5) ∨ (p5 ∧ (((True ∨ False) → (p5 ∨ p5)) ∨ True))) ∨ (((p1 → p5) ∨ p4) → p3)) ∨ True)) := by
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
theorem thm_5_vars_199271331049515577949657151989 : ((((((p2 ∨ p4) → False) → p1) ∧ True) ∨ p1) → ((p1 ∧ ((((p1 ∧ False) ∨ (((p2 ∧ p5) → (p4 → p4)) ∧ True)) → False) ∧ p2)) → p5)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h10 : ((p1 ∧ False) ∨ (((p2 ∧ p5) → (p4 → p4)) ∧ True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h11
      -- Implications on the right can always be decomposed.
      intro h12
      -- Conjunctions on the left can always be decomposed.
      let h13 := h11.left
      let h14 := h11.right
      -- One of the premise coincides with the conclusion.
      exact h12
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h15 := h5 h10
    -- False on the left can always be used.
    apply False.elim h15
  case inr h16 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h17 : ((p1 ∧ False) ∨ (((p2 ∧ p5) → (p4 → p4)) ∧ True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h18
      -- Implications on the right can always be decomposed.
      intro h19
      -- Conjunctions on the left can always be decomposed.
      let h20 := h18.left
      let h21 := h18.right
      -- One of the premise coincides with the conclusion.
      exact h19
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h22 := h5 h17
    -- False on the left can always be used.
    apply False.elim h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111839939787855389602527781886 : (((((p1 ∧ True) ∨ ((False ∧ ((p5 → (((p3 → True) ∧ p5) → p3)) ∧ (False ∧ p3))) ∧ p1)) ∨ ((p5 ∧ p2) → p5)) ∨ p5) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164463658605516085499796427960 : ((((((p5 ∨ ((p5 ∨ ((p4 ∧ False) ∧ p1)) ∧ p2)) ∨ (p1 ∧ p2)) ∧ p5) ∨ p2) ∧ True) ∨ (True ∨ ((False ∨ (p3 ∧ p3)) → (p4 ∧ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42891616949574318857735953972 : (((p3 → ((((((p5 → (True → p3)) ∧ (p5 ∧ p3)) ∨ ((True ∨ (p3 ∧ p4)) ∧ (p1 → True))) ∨ p3) → p5) ∨ (p3 ∨ p1))) ∨ p3) ∨ p3) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303781833665432144119903435745 : (p1 ∨ (((p3 → (p5 → (True ∧ ((((p3 ∧ p4) ∨ p2) ∨ ((p2 ∨ ((p4 → p3) ∨ p5)) → (p1 ∨ (True → p5)))) ∨ p1)))) ∨ p5) ∨ p2)) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257368234672362734154977487609 : ((p2 ∨ p5) → (((((False ∧ (((p5 → True) ∧ p2) ∧ p5)) ∨ p3) ∧ p5) ∨ (p5 → (False → (p4 → (p4 ∨ (True ∧ (p3 → False))))))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h4
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147234786407501313217398288776 : ((((((p2 → ((p2 → p4) ∧ ((False ∧ ((p2 ∨ (p5 → True)) ∧ p5)) ∧ p1))) → p1) → False) ∧ p4) ∨ p2) ∨ (True ∨ ((p1 ∨ False) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



