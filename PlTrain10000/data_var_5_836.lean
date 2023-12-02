variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_144912473242695330869911797846 : ((((p4 ∨ ((p4 ∨ False) ∧ (p4 ∨ True))) → ((p5 ∧ p3) ∨ (False → p3))) ∨ (p1 → ((p1 ∧ p3) ∧ p3))) ∧ ((False → p5) → (True ∨ p3))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h9
        -- False on the left can always be used.
        apply False.elim h9
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- False on the left can always be used.
        apply False.elim h11
    case inr h12 =>
      -- False on the left can always be used.
      apply False.elim h12
  -- Implications on the right can always be decomposed.
  intro h13
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238127761463402320619992102843 : ((True ∨ p3) ∧ ((((((p4 → False) ∧ p4) ∨ p4) ∨ (True → p4)) ∨ (((True ∨ p2) ∧ p2) → ((p2 → (False ∧ p4)) ∧ p3))) ∨ (p4 ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208261787538029864379873372051 : (((p5 ∧ p1) ∧ ((True ∧ False) → False)) → (p3 ∨ (((p3 → (p5 → ((((p4 ∨ p2) → (p3 → p1)) → p2) ∧ True))) ∧ p3) ∨ (p5 → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306588896359431089370437774860 : (p1 ∨ ((True → False) → (p1 ∨ ((((p2 ∨ (p1 → ((True ∨ ((True ∨ (p3 ∧ p4)) ∨ p1)) ∧ p5))) ∨ False) ∧ (p5 → (p5 ∧ p4))) → p3)))) := by
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
theorem thm_5_vars_307969445484262156626168920286 : (p2 ∨ ((((p5 ∨ p4) → (((((True ∨ False) → (False ∨ (p2 ∧ (p4 ∧ True)))) ∧ (p4 ∨ (p1 ∧ True))) ∨ p2) ∨ (p2 ∨ True))) ∨ False) ∧ True)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172685092918643962809262864544 : (((p1 ∧ False) ∨ ((False → ((p5 → p1) ∨ (p3 ∧ p3))) → (p3 ∧ (p5 → p1)))) ∨ ((((False → p2) ∨ p5) ∨ (p2 ∧ (False ∧ p5))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53371447107879500709279068864 : ((((((True → (((False ∧ p1) ∨ p2) → False)) ∨ p5) ∧ p2) → p4) → ((p1 → (((p3 → (False ∨ (p1 ∧ p2))) → p5) → p4)) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_989451348298806577853819996062 : (((p3 ∧ (((True ∧ (p3 → False)) ∧ p1) ∧ ((p5 ∧ ((((p1 → p1) ∨ (False ∧ p1)) ∨ (p4 ∨ False)) → p1)) ∧ ((p2 → p5) ∧ True)))) → False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h5.left
  let h11 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h10.left
  let h13 := h10.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h11.left
  let h15 := h11.right
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h16 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h17 := h9 h16
  -- False on the left can always be used.
  apply False.elim h17
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354760458859743810987433346298 : (p5 → (((p2 ∧ (p2 → ((((p5 → p4) → p2) → p1) → ((p1 ∨ True) ∨ False)))) → (p1 → (((False ∨ p5) ∧ False) ∧ (False ∨ p5)))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56791895396651934213255844346 : ((((True ∨ True) → p3) ∧ (p3 → (p4 ∨ ((p1 ∧ False) ∧ ((True ∧ ((p1 ∧ p3) ∧ (False ∨ (p1 ∨ (p2 ∧ (p2 → True)))))) ∧ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244808187614025060537321020858 : ((p1 ∧ p1) ∨ (((p2 ∧ (False ∧ p2)) ∨ (((p1 ∧ False) ∨ p5) ∧ (((p2 ∧ p3) ∨ p4) ∧ (True ∧ ((p3 ∨ p3) ∧ p3))))) ∨ (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213858671401228281040147387802 : (((False ∨ (p1 → False)) ∨ p3) ∨ ((True ∧ ((p3 ∧ p2) ∨ ((p2 ∨ p1) ∧ (p3 ∨ p3)))) → ((p2 → p4) → ((p4 → (False ∨ True)) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h8 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h9 := h2 h8
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h15 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h13
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h16 := h2 h15
        -- One of the premise coincides with the conclusion.
        exact h16
      case inr h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h18 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h13
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h19 := h2 h18
        -- One of the premise coincides with the conclusion.
        exact h19
    case inr h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h21 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h22
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h23 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h24
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_706901438460175591232000081254 : ((((((((p3 ∧ p3) ∧ p5) ∨ p5) ∨ p1) ∨ p3) ∨ ((True ∨ (p3 ∧ p4)) → (True ∧ (((p5 ∨ (p4 → (p2 ∨ True))) ∨ p3) ∧ True)))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350097247929158253541714153373 : (p4 → (((p1 ∨ ((p3 ∧ ((p4 ∧ (((p1 → p4) ∧ (p2 ∧ p5)) → p5)) ∨ (False ∧ (False → p4)))) → p1)) ∨ ((p5 ∧ True) ∨ False)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329751173879717740549348054469 : (True → (True ∧ ((((p4 ∧ p3) ∨ p2) → ((((p4 → ((((p4 ∧ p3) → (p4 → p2)) ∧ (p1 ∨ p1)) → False)) ∨ True) ∨ p5) → False)) ∨ True))) := by
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
theorem thm_5_vars_250107746466510953482237826019 : ((True → p4) ∨ (((p3 → p2) ∧ (False → p3)) ∨ ((((p4 → (p4 ∨ ((p2 ∨ p4) ∧ p5))) → p5) ∧ (p5 → p2)) ∨ (p3 → (p3 ∧ p3))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301620165922416006606654290675 : (False ∨ ((p1 ∧ (False ∨ True)) → ((False ∧ False) ∨ (p2 → (((p2 → (p4 ∨ ((((False → (True ∨ True)) ∧ p4) ∧ False) ∨ False))) ∧ p4) ∨ True))))) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341667327812210956081212315607 : (p2 → (((p2 → ((p3 ∨ (p4 ∨ (p5 ∧ ((((p5 → p5) ∨ p5) ∧ p2) ∧ (False ∧ p1))))) ∨ ((p1 ∨ p1) → True))) ∧ True) ∨ (False → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166536979996130534136522851629 : ((p5 ∨ (((False ∨ (((p2 ∨ (p2 ∧ p3)) ∧ p1) ∨ True)) ∨ ((p1 ∧ p1) → p4)) ∧ p3)) ∨ ((p1 → p5) ∨ (((p4 → p1) ∨ True) ∨ p2))) := by
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
theorem thm_5_vars_62050722815370472530446504426 : ((p2 ∧ ((p4 → p5) ∨ ((((((((True ∧ False) ∧ (p2 ∨ p2)) ∧ (p2 → True)) ∨ p3) ∨ (p5 ∨ p2)) ∧ p1) → (False ∨ p3)) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_632484938247852722996508152958 : (((((p3 ∨ (((False → p5) ∨ (((p5 ∨ p1) ∨ True) ∨ ((p2 ∨ (False → (True ∨ p4))) → p3))) → ((False → p5) ∧ p1))) → p2) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338139813257910553176027527670 : (p1 → (((p4 → p3) → ((p3 ∧ (p2 → True)) → False)) ∨ ((((p3 ∧ (p4 → (p2 ∨ p3))) ∧ p4) → (True ∨ ((p2 ∧ False) ∨ p1))) ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50318092546476391825196309182 : (((((p5 ∨ (((p3 → (p3 → False)) → p5) → p3)) → True) ∧ ((p3 ∨ (p5 ∧ (p1 ∧ True))) ∧ p4)) ∨ (((p1 ∧ p3) → p5) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259640630531682076227480682033 : ((p1 → False) → (((p5 → p1) ∧ ((p4 ∧ p3) ∨ p3)) ∨ ((False ∧ (True ∨ (True → (((p4 ∨ False) ∨ p2) ∨ p4)))) → (p3 ∧ (p1 ∧ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the left can always be decomposed.
  let h7 := h2.left
  let h8 := h2.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66016569472083469112310107237 : ((p5 ∨ (((p2 ∧ (p3 → (p2 ∨ (p4 → (((p1 → (p3 ∧ (p2 → p1))) ∨ (True → (False → p1))) ∧ (False → p4)))))) → p1) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148755719088533926516434946277 : (((False ∨ (p1 ∨ (p3 ∨ (p2 ∨ p2)))) ∧ ((((True ∨ p3) → (p4 ∨ True)) → ((p3 → p2) ∧ p3)) ∧ p1)) ∨ ((p2 ∨ (False → p3)) ∨ p2)) := by
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
theorem thm_5_vars_52135960706352473864429385296 : (((((((p4 → p3) → (p3 ∨ True)) ∨ (False ∨ (p2 ∧ p1))) ∧ p3) ∨ (True ∨ p5)) → ((p2 ∨ (p5 → True)) ∧ ((False ∧ p5) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52259553838455648238172264296 : (((p3 ∨ ((True ∧ False) ∨ (((((p5 ∨ (p5 ∨ p2)) ∨ False) ∨ True) → p2) ∨ p2))) → (p1 → ((p2 ∨ True) ∧ ((p1 → p2) ∨ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249758434672874113222337650990 : ((p5 ∨ p5) ∨ (False ∨ ((p5 → ((p1 ∨ (((p5 ∧ ((False → (p1 ∧ p3)) → p1)) ∨ (p3 → True)) ∨ (False → False))) ∨ True)) ∨ (p4 ∨ True)))) := by
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
theorem thm_5_vars_311165350948633779093044952739 : (p2 ∨ ((p4 ∧ p5) → (p1 ∨ (((((p3 ∧ (((p4 → ((p5 ∧ p4) ∧ p4)) ∨ p3) ∧ p3)) ∨ (False ∨ p5)) ∨ p5) ∧ (p2 ∨ p4)) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61824267647166655770482991095 : ((p2 ∧ ((p1 ∧ ((((p4 ∧ p5) ∧ p5) ∧ (p1 ∧ ((((False ∧ (False ∧ p3)) ∨ p5) ∨ p4) → p3))) ∨ (p2 → (p4 → p2)))) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216049083323887022998595970987 : ((p5 ∨ (p2 ∧ (p4 ∨ p5))) ∨ ((p2 ∨ (((p1 ∧ p5) ∧ True) ∨ (True ∨ ((p1 → (((False ∧ p5) ∧ p4) ∧ p5)) → p4)))) ∨ (False → p4))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38817860174869417406768874052 : (((((p1 → p4) ∨ (p2 ∨ p4)) → ((p2 ∧ (p1 ∧ True)) ∨ (((p4 → p4) ∧ (p5 → ((p1 ∨ p2) ∨ (p1 ∨ p3)))) ∨ p5))) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713203998984554440234770556105 : ((((p2 ∨ (((p3 → p1) → p3) ∧ True)) ∨ ((p5 ∧ p3) ∨ (((p1 ∧ (p5 ∧ ((True ∨ False) ∨ p3))) ∨ p2) ∨ ((False ∨ True) ∨ False)))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_597492457232694717936543311171 : (((((False ∧ ((p3 ∨ p2) ∧ p2)) ∨ (p1 → ((True ∧ (False ∨ (((((p4 ∧ p1) ∨ False) ∨ p1) ∨ False) ∨ p5))) ∨ (p1 → p3)))) ∧ True) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68600841259968948484973315529 : ((p4 → (((((((True → ((p5 ∧ ((p4 ∨ (p2 ∨ (False ∧ p3))) ∨ False)) ∨ p3)) → p2) ∨ (p5 ∨ p4)) → p5) → False) ∨ p4) ∨ p1)) ∨ p2) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1824415028402398440088803334 : ((((p1 ∧ (((p2 ∧ (p5 ∧ p4)) ∧ p4) ∨ (((((p2 ∨ p4) → p3) ∨ True) → p5) ∨ False))) ∨ p2) ∧ p2) → ((p4 ∧ False) ∨ p2)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h16 =>
        -- False on the left can always be used.
        apply False.elim h16
  case inr h17 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114002936209134884769775675702 : (((((p3 ∧ (p5 ∨ (((False ∨ (p3 → (p4 ∨ p2))) ∧ p2) ∧ (p1 ∨ (p3 ∧ False))))) ∨ p1) ∧ p1) ∨ (p2 ∨ (p3 → p4))) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351821384397089904848279990033 : (p4 → ((((p5 ∧ (p4 → p4)) ∧ p5) → (((False ∧ p2) ∧ True) ∨ p1)) ∨ (((p4 → p4) ∨ ((p1 → ((True ∧ p1) ∨ p2)) ∨ p4)) ∨ p2))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613679746805963191716618118688 : (((((((p1 ∧ ((False ∨ p5) ∨ False)) → True) ∧ ((((p4 → p3) ∧ (p3 → p2)) ∧ p3) ∧ (p1 ∧ p2))) ∧ (p5 ∨ (p5 ∧ p1))) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_180196077503983352183859802653 : (((((p2 → p4) ∨ True) ∨ (((p1 ∧ (p3 ∧ p2)) ∧ p4) → p3)) → p1) → ((((((False ∨ False) → p5) → p5) ∧ p2) ∨ (True ∨ p1)) ∨ p1)) := by
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
theorem thm_5_vars_172237394037309795718874503258 : ((((p2 ∨ (p4 ∧ ((p1 → p2) ∨ p5))) → p1) ∧ (p5 → (True ∧ (p2 → False)))) ∨ ((((p3 ∨ p4) ∧ p4) ∧ (p1 ∧ p1)) → (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51439572889051963602396022102 : (((((p5 → ((p2 ∧ ((p1 → p3) ∧ (p1 ∨ p1))) ∨ p2)) → (p3 ∨ p5)) → (p2 ∨ False)) → ((p2 ∧ False) ∨ (p4 ∨ (p2 ∨ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_940290822374816908374431521357 : (((((p5 → (p1 ∨ (True ∨ p3))) ∧ True) → ((((p2 → p4) ∨ p4) ∧ ((((((True → p5) → False) ∧ False) → p3) ∨ p1) ∧ p2)) ∧ False)) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p5 → (p1 ∨ (True ∨ p3))) ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617557991319296776839657362544 : (((((False ∧ (p5 ∧ (p2 ∧ (p5 ∨ p3)))) ∧ ((True → (((False ∧ False) → ((p5 ∨ True) ∨ p4)) ∧ p3)) → (p2 → (p4 ∨ p2)))) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_113847317927253377687188714736 : (((p5 ∨ (True ∧ (((False → p1) ∨ p5) → (p3 ∨ (((True ∧ p2) ∧ ((p2 ∨ (True → p5)) → p5)) ∨ False))))) → (p5 ∧ True)) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670724982614642009356482998727 : ((((True ∧ ((p2 ∧ (p5 ∧ p5)) ∧ (p3 → ((p5 ∧ ((p4 → p5) ∧ True)) ∨ ((p4 → (p4 ∧ p4)) → p2))))) ∨ (False → (p1 ∧ False))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52449756131980538337207758949 : (((p3 ∧ ((p1 ∧ (p4 ∧ (p4 ∧ (True → p3)))) → (True ∨ (p3 ∨ p4)))) ∧ (False ∧ (((True ∨ (True ∨ (p1 ∨ p2))) → False) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_78165015301719305786263232735 : (((p1 → ((True ∧ True) → (p3 ∨ (((p2 → (p3 ∧ (p3 ∧ (p1 → (True → p1))))) ∨ (p2 → p4)) ∨ ((p2 ∨ p5) ∨ True))))) → False) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 → ((True ∧ True) → (p3 ∨ (((p2 → (p3 ∧ (p3 ∧ (p1 → (True → p1))))) ∨ (p2 → p4)) ∨ ((p2 ∨ p5) ∨ True))))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h2
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158975501776137518514282393552 : ((p3 ∨ ((p1 → (p4 → ((p2 ∧ ((p3 ∨ ((p5 ∧ p1) ∨ (p2 ∨ p2))) ∨ p2)) → False))) → p4)) ∨ (p4 → (((p3 → p2) → p4) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_428235554830380066099681156918 : (((((((True ∨ (p3 ∨ ((((p3 ∨ (p2 ∨ p1)) ∨ p4) → True) ∧ (p3 → False)))) → (p1 ∨ (p4 → p1))) → p5) → p1) ∨ (p2 → p2)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341706570370893684599520143534 : (p2 → ((((((p1 ∨ p4) ∨ p4) → p1) ∨ ((p4 ∨ (p4 ∨ (False ∧ (False ∨ p3)))) ∨ False)) ∨ (True ∨ ((True → True) ∨ p2))) ∨ (p1 ∧ p1))) := by
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
theorem thm_5_vars_785998354884177025707858084182 : (((p4 ∨ ((p5 ∧ (((p1 ∧ False) ∧ (p1 ∨ p3)) ∧ (((p3 → (p5 ∨ (p1 → False))) → ((p5 ∨ p5) ∧ p1)) → p1))) ∨ (p2 → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111753864856038092610339734646 : ((((p5 → (p4 → (((((False ∧ p5) ∨ (True ∨ p3)) ∨ ((False → (p5 → (p3 → p2))) ∧ p2)) → p1) ∧ p3))) → p3) ∨ False) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158039302342138369631354269547 : (((((p3 ∨ (p1 ∨ p5)) ∨ False) ∨ p1) ∨ ((p1 ∧ p5) → ((p2 ∨ False) ∨ (True → (p5 ∧ p5))))) ∨ (((p2 ∧ p2) ∧ (p5 ∨ p2)) ∨ p5)) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67853964261934159736244482266 : ((p2 → (((p5 → (p3 ∨ p4)) → (p2 → (p2 ∨ ((((p5 → (p5 → False)) ∨ p2) ∨ (p1 ∧ p3)) → (False → True))))) → (p2 → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_631221324647892247882694310285 : (((((((((True ∧ p1) ∧ (False → p1)) ∧ (((p4 ∨ ((p3 → True) → p2)) ∨ (False → p3)) ∧ p4)) ∨ (p4 ∨ p1)) → p4) → p2) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42622207272000467329534194648 : (((p3 ∨ (((((p4 → (p3 ∨ p4)) ∨ True) ∨ p3) ∧ (p3 ∨ (p1 ∧ p4))) ∧ ((p2 → p1) ∨ (p2 ∧ ((p3 ∧ False) ∨ True))))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_83298930034163369600218626849 : ((((p5 → (p3 ∨ (((True → (p1 → p5)) → True) ∨ p1))) ∧ (False → ((p2 ∨ False) ∧ p5))) ∧ (True → ((p1 ∨ (p2 → p5)) ∧ p2))) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51496851837651718750311381807 : (((((True → p3) ∧ p2) ∧ (((p3 → (p2 ∨ p2)) → ((True → p1) ∧ p5)) ∨ (p5 ∧ False))) → ((p2 → False) ∨ ((p3 → False) → p4))) ∨ p1) := by
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
  cases h3
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : p3 := by
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h9 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h10 := h4 h9
      -- One of the premise coincides with the conclusion.
      exact h10
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h11 := h7 h8
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245115997357548901602339419196 : ((p2 ∧ True) ∨ ((((((p5 ∧ ((p4 → p2) → p1)) ∨ (p4 ∨ p5)) → (p2 ∧ (p2 ∧ p1))) → (True ∧ p4)) → p3) → (p3 ∨ (p5 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147387747834715013066947347120 : (((((((True ∧ p5) → p5) ∧ True) ∨ (p1 ∨ p4)) ∧ ((((True ∨ (p4 → p3)) → False) ∨ False) ∨ p2)) ∨ False) ∨ (((True ∧ p5) ∧ p4) → p5)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134157883328293638289245382897 : (((((((True ∨ (p5 → True)) ∨ ((p2 → False) → p3)) ∧ (True → p2)) ∨ (p5 ∧ True)) → (p5 ∧ (True → True))) ∨ p3) ∨ ((p3 ∧ False) → p3)) := by
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
theorem thm_5_vars_84056344907855900676635022451 : (((((p4 → (True ∨ (p2 → (False ∧ (False ∧ p1))))) ∧ p4) ∧ ((p4 → p5) ∧ p1)) ∧ (((True ∨ (p4 ∨ False)) ∨ (p1 ∨ False)) → p5)) → p1) := by
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
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51636378643622535464337943454 : (((((p4 ∨ (((p5 ∨ p5) → (p2 → (False ∨ (p3 → p2)))) ∧ p1)) → True) ∨ p5) ∧ (((p4 ∨ p4) → (p5 ∨ p2)) → (p4 ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148601703694142285153432467840 : (((p4 ∨ ((p1 ∧ ((True → (True → p3)) → p4)) ∧ p3)) ∨ ((p2 → (p4 → p5)) → ((p1 → p3) → p5))) ∨ ((False ∧ (p1 ∧ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317708279730647292706341127809 : (p4 ∨ (((((False ∨ p1) → (p4 ∧ (p1 ∧ True))) ∧ ((p4 → (p2 ∨ p2)) → ((p2 ∨ ((False → False) ∧ p1)) ∨ p3))) ∨ (p2 → True)) ∨ p5)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112750017515531360193077971026 : (((((True ∨ p2) ∧ (p3 → (True → ((False ∧ False) → (False → p3))))) → (((p5 ∧ False) → p5) ∧ ((False ∨ p5) → p5))) → p5) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_106145227861203059474523807033 : ((((p1 → True) ∧ (p1 ∧ (p3 → ((p1 ∨ p4) ∨ (p1 ∧ p4))))) ∨ (p3 → ((False ∨ (((False ∧ p5) ∧ p3) ∨ p2)) → p2))) ∧ (p2 → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- False on the left can always be used.
      apply False.elim h8
    case inr h10 =>
      -- One of the premise coincides with the conclusion.
      exact h10
  -- Implications on the right can always be decomposed.
  intro h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260784359786315002251960446429 : ((p3 → p5) → ((((((p5 ∨ p3) ∧ (((False ∨ (p5 → p4)) → (p3 → p1)) ∨ p5)) ∨ p5) ∧ p5) → (p4 ∧ p4)) → ((True → p1) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179391317538778586396527093450 : ((p3 ∨ (((p5 → False) ∨ ((False ∧ (True ∨ False)) → p3)) → (p1 ∨ p1))) ∨ ((((p5 ∧ p2) ∨ False) ∨ (p2 → ((p3 ∧ p3) ∨ True))) ∨ False)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136229081293168719170973638436 : (((((p2 ∧ p1) ∨ p1) ∧ (p1 ∧ p2)) ∨ ((False ∨ ((p4 ∨ (p3 → False)) ∨ True)) ∧ ((p5 → p4) ∧ (p5 ∧ True)))) ∨ (p5 ∨ (True ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179201122776892869793961836869 : ((p3 ∧ (p5 ∨ ((p1 ∧ p5) ∨ ((p4 ∨ ((p1 ∨ p3) → True)) ∧ True)))) ∨ (p3 → (((p4 ∨ p1) ∨ ((p3 → p5) ∨ p5)) → (True → True)))) := by
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
theorem thm_5_vars_111329489001915475898436832577 : (((p2 ∧ (((((p1 ∧ (p4 ∨ p2)) ∧ p5) → (p2 ∧ p1)) ∨ p5) → (p2 → (p4 ∧ (p5 → (p5 ∧ (False ∨ False))))))) ∧ p1) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_861414723645735834701619697477 : (((((p1 ∧ (((p1 ∨ p2) ∨ (((p1 ∨ False) → True) ∨ p4)) ∨ (((p5 ∧ True) → p4) ∧ (False ∨ p3)))) ∨ (False ∨ (p2 → True))) → p4) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p1 ∧ (((p1 ∨ p2) ∨ (((p1 ∨ False) → True) ∨ p4)) ∨ (((p5 ∧ True) → p4) ∧ (False ∨ p3)))) ∨ (False ∨ (p2 → True))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_21523088363751366843889563062 : ((((p5 ∨ p4) → ((p3 → ((p4 ∨ p1) ∧ p3)) → p1)) ∨ ((False → (((p1 ∨ p1) ∧ (True ∨ p3)) → ((p1 ∧ False) ∧ p3))) → True)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134028551527647308936023146913 : (((((True → ((p5 ∧ ((False ∨ (p1 → p2)) → (p5 ∨ p5))) → (((False → p3) → p1) → p2))) → p4) ∨ p5) ∨ True) ∨ ((p5 ∧ p4) ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_649461731638844752539227903566 : ((((((((p1 ∧ False) ∨ (p3 ∨ ((p2 ∨ (p2 ∨ p4)) ∨ p1))) ∨ True) ∨ ((False → p1) → (p5 ∨ p4))) ∧ (True ∧ p4)) ∧ (True ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308596166187536812454380891996 : (p2 ∨ ((((p2 ∧ p4) ∨ p5) → ((((p3 → False) → p4) → (((False ∨ p1) ∧ True) → (p5 → True))) → ((p1 ∧ (p3 ∨ p5)) → p3))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54528304081213084055912645492 : ((((False ∨ p5) ∨ (((p5 → False) ∨ p2) → p3)) ∨ (((True → (p5 ∨ ((((p5 ∨ p4) ∨ False) ∨ (p3 ∨ p5)) ∨ True))) ∧ p5) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228868365342523881026568536993 : ((p4 ∨ (True ∧ False)) ∨ ((((True ∨ ((False ∨ ((((p2 ∨ p4) ∧ (p3 ∨ True)) ∨ p3) ∨ p2)) → (p1 ∧ p2))) → (p4 → p5)) ∨ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729972095480882330298374484178 : (((((p5 ∧ p2) → p3) → ((((((True ∧ (p1 ∧ True)) → (p2 → (p2 ∧ p2))) ∧ p1) → ((p1 ∧ p1) ∧ p5)) → (False ∧ p1)) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114875017872931600375044109776 : (((((True ∧ p2) ∨ p3) ∨ (((p5 ∧ (p5 ∨ p4)) ∨ p5) → (p5 ∧ p2))) ∨ (((p2 ∧ p5) ∧ p5) → (p5 ∨ (True → p3)))) ∨ (p5 ∨ p3)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179794243192456349668830384207 : ((((True ∧ p2) ∧ (p5 ∨ ((p2 ∧ ((p2 ∧ p2) ∨ p3)) → p5))) ∧ p4) → (((((p1 ∨ (p2 ∧ p5)) ∨ False) ∧ p5) ∧ (False → False)) ∨ False)) := by
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
  cases h5
  case inl h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h7
    -- One of the premise coincides with the conclusion.
    exact h8
    -- One of the premise coincides with the conclusion.
    exact h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h11 : (p2 ∧ ((p2 ∧ p2) ∨ p3)) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h7
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h7
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h12 := h10 h11
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h7
    -- One of the premise coincides with the conclusion.
    exact h12
    -- One of the premise coincides with the conclusion.
    exact h12
    -- Implications on the right can always be decomposed.
    intro h13
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_131585337523883935502382683963 : ((((p2 ∨ False) ∧ True) ∨ (((((((p2 → True) ∧ (False ∨ p4)) ∨ p2) ∧ True) ∨ False) ∨ ((p5 ∨ True) → True)) ∨ True)) ∧ (False → (p5 → p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609473927914337251747756174561 : (((((False ∧ (((p1 ∧ p3) ∧ False) ∨ (p3 ∧ ((p1 ∧ (p4 ∨ True)) ∨ (((True → False) ∧ True) ∧ (p2 ∧ (p4 ∧ p4))))))) ∨ p1) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609363461186022667252335505102 : ((((((p5 ∨ p2) ∨ ((((False ∧ (False ∨ (True ∧ ((p2 ∨ (p3 → p5)) ∧ False)))) → (p4 ∧ p5)) → (p4 ∧ True)) ∨ False)) ∨ False) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185686648575730719492489078106 : ((p1 → (False ∧ (((False ∨ False) → (p2 ∧ (False ∧ p2))) → p2))) ∨ (((p5 → False) ∧ ((p5 ∧ p5) ∨ p4)) ∨ ((p3 ∨ True) ∨ (p2 → False)))) := by
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
theorem thm_5_vars_208734091625678137666359309860 : ((p1 ∧ ((p5 ∧ p1) → (p4 ∨ False))) → ((((((p4 ∨ p2) ∧ p2) ∧ (p4 ∨ (p5 ∧ False))) → False) ∧ ((p2 → (False ∨ p1)) ∨ True)) ∨ True)) := by
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
theorem thm_5_vars_698931132411720880220256914885 : ((((p4 ∧ ((((False ∧ True) ∧ (p3 ∨ False)) ∨ (False ∨ False)) ∧ p2)) ∨ (p1 → (p1 ∨ ((p5 → (((False → False) ∨ p5) → p5)) → p1)))) ∨ p3) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346901566329311662462079143816 : (p3 → ((((True ∨ p2) ∨ (False → (((False ∧ p5) ∧ (True ∧ ((False → p3) → p3))) ∧ p1))) → p2) ∨ (((False ∧ p3) → p5) → (True ∧ True)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352845568276150152756062778512 : (p4 → ((p3 → p5) → ((((True ∨ ((((p2 ∧ p1) → True) ∨ p3) ∨ p1)) ∧ p4) ∧ (False ∨ True)) → (True → ((p5 ∧ (True → p1)) → p5))))) := by
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
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h3.left
  let h9 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h13 =>
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h18 =>
          -- False on the left can always be used.
          apply False.elim h18
        case inr h19 =>
          -- One of the premise coincides with the conclusion.
          exact h6
      case inr h20 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h21 =>
          -- False on the left can always be used.
          apply False.elim h21
        case inr h22 =>
          -- One of the premise coincides with the conclusion.
          exact h6
    case inr h23 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h24 =>
        -- False on the left can always be used.
        apply False.elim h24
      case inr h25 =>
        -- One of the premise coincides with the conclusion.
        exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65740890452535584761913431917 : ((p4 ∨ ((((p4 → (True → True)) → ((p2 → (p5 ∧ ((p3 → p4) → (p1 ∨ p3)))) ∨ True)) → (p3 → False)) ∨ (p4 ∧ (True → p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_640106600438967934708935354156 : ((((((p2 → p2) ∧ p2) → ((((False ∨ (p1 ∨ (((p5 ∨ p3) ∨ p3) ∧ p5))) → ((p1 → p3) ∨ p1)) → p1) ∧ (True ∧ p2))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158368651603375047626509991014 : (((p3 ∨ p3) ∧ (p2 ∧ (((True → ((p1 ∨ (False → (p2 ∨ False))) ∨ (p1 → p5))) → True) → False))) ∨ (((p5 ∧ p5) ∧ (p4 ∧ p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329734887412552411230786067674 : (True → ((p4 → p4) → (((p3 ∨ ((False ∨ ((p5 → (p2 ∧ p1)) → ((p2 ∨ False) → (False ∧ False)))) ∨ p3)) ∧ (p2 ∨ (p5 ∧ p1))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59274154948521829029624388487 : (((p3 ∨ p1) ∨ (((p2 ∧ (p4 ∧ p1)) ∨ (p4 → p1)) → (((p4 ∨ (False ∧ (False ∧ p5))) ∨ ((p4 → p4) ∧ True)) ∨ (p2 ∧ p1)))) ∨ p1) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h8
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61575448080617855317463723347 : ((p1 ∧ ((True ∨ (False ∨ (p1 ∨ p2))) ∧ (((p5 ∨ ((((p4 ∨ p2) ∧ p1) ∨ ((p3 ∨ True) → p5)) ∧ p5)) ∨ p4) ∧ (True → False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159232027888467043416537424923 : ((p3 → ((((p1 → p3) ∧ (p5 ∨ p2)) ∧ ((p4 ∨ p2) ∧ (p4 → (p4 ∨ (p1 ∧ p1))))) ∨ p2)) ∨ ((True ∨ (p1 → True)) ∨ (p3 ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134095462540846499469168589356 : ((((True ∨ (((False ∨ (p2 → True)) ∧ (True ∧ ((p4 ∧ p5) ∨ ((p3 ∧ False) ∨ (False → p4))))) ∨ p4)) → p5) ∨ p5) ∨ ((p3 → True) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



