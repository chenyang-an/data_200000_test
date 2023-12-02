variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117298786084785516535019588333 : ((False ∧ ((((p5 ∧ (((p1 ∧ (((False → p5) → False) ∧ p1)) ∧ p3) ∨ p1)) ∨ p4) ∨ (True → (p1 ∧ p1))) ∨ (p4 → p5))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_755275475029859484142872966326 : (((p1 ∧ ((((((((False ∧ False) ∨ p3) → (True → ((p4 ∨ True) ∨ p2))) ∧ (p3 ∨ (p3 ∧ (True ∧ p4)))) → p1) ∧ p3) ∧ True) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60156692134756899799364039541 : (((p4 ∨ p4) → ((((p1 ∧ (((p3 ∨ False) ∧ p2) ∧ True)) → p3) → p1) → (((p3 ∧ p1) ∧ p4) ∧ (True ∨ ((p3 ∨ p4) → p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181508475424491091071914325544 : ((p5 ∨ (p4 ∧ (((p1 ∧ ((p3 → (p5 → p1)) ∧ p3)) ∧ p3) ∧ True))) → (((p1 ∨ p2) ∧ (((p2 → (p1 ∧ p1)) ∨ p4) ∨ p2)) ∨ True)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60610917693521129298797437809 : ((True ∧ (((p1 ∧ (p5 → (((p3 ∨ (p1 → True)) ∧ ((p5 → False) ∧ (p3 ∨ p4))) ∨ ((False ∨ p3) ∨ p1)))) ∨ p1) ∨ (False ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51942058006575627732564596474 : ((((((p4 ∨ (True → p2)) ∨ p5) → (True ∨ True)) → ((p5 ∨ (True ∧ p1)) → p5)) ∨ ((((p4 → True) ∨ (p3 → False)) ∨ p5) → True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238738638972310413695234884087 : ((p1 ∨ True) ∧ (((((True ∧ ((p2 ∨ (p2 → p3)) ∧ p3)) → p1) ∨ ((p5 ∧ p3) ∨ p4)) ∨ (True ∨ (p5 ∧ p4))) ∨ (False ∨ (p4 ∧ False)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39347336596802256435518453502 : (((p2 ∧ (p3 ∨ ((((p3 ∨ (((p5 ∨ False) ∧ (((p4 → ((p1 ∨ p5) → p2)) ∧ p2) ∨ p1)) → p4)) ∨ True) → p1) ∨ p5))) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42747122012602459904982602361 : (((True → ((p5 → (p3 → p1)) → ((((((p1 ∨ (p2 ∨ p3)) ∨ (p1 → p1)) → p1) → (True → p5)) ∧ p4) ∨ (False → p2)))) ∨ p2) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166019349377952007004431328858 : (((p4 ∨ p1) ∨ ((p5 → (p2 → (False ∧ True))) → (True ∧ (((p1 ∧ p4) ∨ p2) → p4)))) ∨ (((False ∧ ((p3 ∧ p4) ∧ False)) → p3) ∨ p4)) := by
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
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193766677254419299308336823433 : ((p3 ∧ (p4 ∨ (True → ((True → (p4 ∨ p5)) → p4)))) → (p4 ∨ ((((((p1 ∧ True) ∨ p2) ∧ ((False ∧ p2) → True)) → p1) ∨ True) ∧ p3))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342383353283374177493484114512 : (p2 → (((((p5 ∨ p2) ∨ (p3 → ((p5 ∧ ((p1 → p3) ∧ p1)) ∧ p2))) → p2) → p3) ∨ ((True ∨ p2) ∨ ((p1 ∧ p5) ∨ (p1 ∧ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_757075100781166636524028381226 : (((p1 ∧ (((p2 → p1) ∨ p5) ∧ ((p3 ∧ p3) ∧ ((((True ∨ True) ∨ ((p2 ∧ (p4 ∨ p3)) ∧ (p4 ∧ p5))) → (p5 ∨ p2)) → True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698155222955221892489440940975 : ((((((p1 ∨ (((True ∨ p1) → p2) ∧ (p1 ∨ p5))) ∨ p1) → False) ∨ ((p2 → p1) → (((p4 ∨ (p5 ∧ False)) ∧ (p1 ∧ False)) → p2))) ∨ False) ∧ True) := by
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
    -- False on the left can always be used.
    apply False.elim h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319473551245832615312682478756 : (p4 ∨ ((p4 → (((((p4 → False) ∧ p3) ∧ p2) ∨ (False ∨ p2)) ∨ False)) ∨ (True ∨ (p2 ∨ (((p4 ∧ ((False ∧ p2) ∨ p3)) ∧ False) ∧ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_202028301622212962715000169602 : (((((False → p1) → False) ∧ True) → False) ∧ ((p2 ∧ (p1 → p2)) ∨ ((p4 → ((p4 → ((p3 → p4) ∧ (p5 → p3))) ∧ p3)) ∨ (p5 → p5)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (False → p1) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- False on the left can always be used.
  apply False.elim h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h7
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_120144208969276874363692145965 : (((((p2 → p3) ∨ True) → (p3 ∨ (((False → p5) → (((True → p4) ∨ False) → ((p5 ∨ p1) ∨ p1))) → (p4 → p1)))) ∧ True) → (p4 → p4)) := by
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
theorem thm_5_vars_343642603899664907527157451996 : (p2 → (True ∧ ((((p4 ∨ False) ∧ True) ∨ ((p4 ∨ (True → p5)) → p3)) → (((p3 → p1) ∨ (((p3 ∨ p1) ∨ p2) ∨ True)) ∨ (p5 ∧ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h7
  case inr h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157624023644298579760066838895 : ((((((p2 → p4) ∨ p3) → (p1 ∧ p2)) ∧ ((p3 ∨ (True ∧ p5)) ∨ p1)) ∧ ((False ∨ p4) ∨ p4)) ∨ ((p2 ∧ (p2 → False)) → (p3 ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h9 := h7 h8
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114331144873495723799044161239 : (((False ∧ (p5 ∧ (((p5 ∧ (True → (True → p1))) ∨ (p5 ∧ p4)) ∧ (p2 ∨ (p3 → p1))))) ∧ (True ∧ ((p1 ∧ True) ∨ p5))) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187475308556460520441763890628 : ((False ∨ (((p2 → p3) ∨ (p2 ∧ (p2 ∧ (False ∨ p2)))) ∧ p4)) → ((True → ((((p1 ∧ p1) → False) → False) ∨ ((p3 ∨ True) ∨ p5))) ∧ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- False on the left can always be used.
        apply False.elim h13
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h15 =>
    -- False on the left can always be used.
    apply False.elim h15
  case inr h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h19 =>
      -- One of the premise coincides with the conclusion.
      exact h18
    case inr h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- Conjunctions on the left can always be decomposed.
      let h23 := h22.left
      let h24 := h22.right
      -- Disjunctions on the left can always be decomposed.
      cases h24
      case inl h25 =>
        -- False on the left can always be used.
        apply False.elim h25
      case inr h26 =>
        -- One of the premise coincides with the conclusion.
        exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117667329750309030294622239185 : ((p3 ∧ (((((True ∧ False) ∨ p1) → (((p5 → (p3 → p3)) → p2) ∧ False)) ∧ True) ∧ (((True ∧ (p5 → p3)) ∨ p1) ∧ True))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658564267948434119694953695843 : ((((p2 ∨ (p1 ∨ ((((p1 ∨ p5) → p2) ∨ ((p5 ∨ True) → (((True → (p2 → False)) → (p5 → p5)) → p2))) ∧ True))) ∨ (p3 ∨ True)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_625659752216472116670603140169 : ((((p1 → (((((p1 ∨ p2) ∨ (p3 ∨ ((p5 → p3) → ((p2 ∨ (p5 ∨ p4)) ∧ p3)))) ∨ (False → p1)) ∧ p5) → (False ∨ True))) ∨ p4) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65151595866285820731057173390 : ((p2 ∨ (p5 → ((p5 → ((False ∨ (p2 → (p2 ∨ (((True → (p2 ∨ p4)) ∨ (p5 → False)) → ((p2 → p4) ∧ p1))))) → p2)) ∨ True))) ∨ False) := by
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
theorem thm_5_vars_113703569893219003419143499838 : ((((p4 → (False ∧ ((p4 → (((p2 → p1) ∧ (p1 ∨ p1)) ∧ p3)) ∨ ((True ∨ p2) ∧ (p3 ∨ p2))))) → p2) → (p5 ∨ p2)) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192450260826421117374992944341 : ((((p4 → ((p5 ∨ p3) → (True → p4))) → False) ∨ p1) → (p1 ∨ ((((True → p3) → (((p2 → p4) ∧ p4) ∧ p2)) ∧ (p1 → False)) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : (p4 → ((p5 ∨ p3) → (True → p4))) := by
      -- Implications on the right can always be decomposed.
      intro h4
      -- Implications on the right can always be decomposed.
      intro h5
      -- Implications on the right can always be decomposed.
      intro h6
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h7 =>
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h8 =>
        -- One of the premise coincides with the conclusion.
        exact h4
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h9 := h2 h3
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147378489658249644345519964975 : (((((p4 ∧ p4) → (p1 ∧ ((True ∧ p5) ∧ (True → p1)))) ∧ (p2 ∨ ((p3 ∧ (p3 ∧ p3)) ∨ False))) ∨ p5) ∨ (p5 → (p2 ∨ (p1 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111711369290485334320380131164 : (((((((p5 ∧ (True → (p5 → p2))) ∧ True) → ((p4 ∧ p3) ∧ p4)) ∧ (p5 ∨ ((p5 ∧ (p4 ∧ p1)) → False))) → p4) ∨ True) ∨ (p3 ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157813405788991844909891880876 : ((((p1 ∧ (False ∨ (p5 → ((p4 → (p4 → p3)) → p4)))) → p3) → ((p2 → (p1 ∨ p3)) → False)) ∨ (False → ((p2 ∧ p2) ∨ (p1 ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136166877880008406133079227480 : (((p3 → (False → ((p5 ∨ p3) → (False ∧ p3)))) → (((p1 ∨ (p1 → p4)) → ((p5 ∨ (p5 ∧ p5)) ∧ p5)) → p4)) ∨ ((False ∧ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720536186777813819662467041369 : (((((p2 → (True ∧ False)) ∨ True) → (((p2 ∧ ((p2 ∨ True) → (p3 ∨ (p4 ∧ p4)))) ∨ p1) ∨ ((False ∧ p1) ∧ ((p2 ∧ p1) ∨ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45180798277025449165180541614 : (((True ∧ (p3 ∨ ((p4 → (((p4 ∧ p5) ∨ ((((p2 → False) ∧ p3) → p5) ∧ (p1 → p2))) ∧ (p3 ∧ (p5 ∧ p1)))) ∨ p5))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_237874024083826488094012329151 : ((True ∨ True) ∧ ((((((p4 → p2) → p1) → p4) ∧ (p4 ∨ (p1 → p5))) ∨ ((p5 → (True → True)) ∧ (p2 → (p3 ∨ (False → True))))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118649590887647483856127191767 : ((p4 ∨ (p1 ∧ ((p2 → False) ∨ (((p3 → False) → True) ∧ (p1 ∧ (p3 ∨ (p4 ∧ ((((True ∧ False) → p3) → p3) ∨ p4)))))))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171969768443454918393702093968 : (((p3 ∧ ((True → ((p5 ∨ (p5 ∨ p1)) → (True → p1))) ∧ False)) ∧ (p1 ∧ p5)) ∨ (p3 → ((True ∧ ((p2 ∧ p2) ∨ True)) ∨ (p5 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183743814657534202549737454197 : ((p5 → ((p4 ∨ (p5 ∨ (((False ∧ p4) ∨ False) ∨ False))) ∨ p5)) ∧ ((True → (((p1 ∧ ((p5 ∧ p5) ∨ p1)) ∨ True) → False)) → (p3 → p1))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : ((p1 ∧ ((p5 ∧ p5) ∨ p1)) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138981274199288589283812646810 : (((((((p5 ∧ False) ∨ ((p1 → p3) ∧ ((p2 → (p1 ∨ (p1 → p5))) ∧ (p2 ∨ False)))) → p1) ∨ False) ∨ p2) ∨ p2) → (p3 ∨ (True ∨ p4))) := by
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
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h5 =>
        -- False on the left can always be used.
        apply False.elim h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42852878072012655231373114618 : (((p2 → ((p5 ∧ (((p5 ∨ p5) ∨ p5) → (((p2 ∧ (((p1 ∨ p4) ∧ p5) ∧ (p5 ∨ p3))) → p3) ∧ True))) ∨ (p4 → True))) ∨ p5) ∨ p4) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39007794915716000201029197114 : ((((p4 ∨ True) ∧ ((((p1 → False) → False) ∨ (False ∧ ((p3 → ((p2 ∧ True) ∧ True)) ∧ ((p5 ∧ p2) ∧ (p3 ∨ False))))) ∨ True)) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317141655463930606113367039481 : (p3 ∨ (p5 → (p4 ∨ (p2 ∨ (((((((p1 ∨ (p4 → p2)) ∨ False) ∧ True) ∧ p4) → False) → ((p1 ∨ p5) ∧ p3)) ∨ ((True ∧ True) ∨ p3)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62937703458320983076490789713 : ((p4 ∧ (p3 ∧ (((((p2 → p3) → (p3 → (False ∧ p2))) ∧ (p2 ∧ p5)) ∨ p2) ∨ (((p2 → p1) ∨ p4) ∧ ((False ∧ p2) → p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_792110927100450384473564750330 : (((True → (((p1 ∨ (False → (p3 ∨ False))) → ((p3 → (((p5 ∨ p4) ∨ (p1 ∧ True)) ∨ (False ∨ p3))) ∨ p1)) ∨ ((p4 → p3) → p2))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_109565024339523829277839821130 : ((p3 ∨ ((p3 ∧ (p3 ∨ (((p4 ∧ p1) ∧ (False → True)) ∧ (p3 → (False ∧ (p1 ∧ p2)))))) ∨ ((p5 → p5) ∨ (True → False)))) ∧ (False → p2)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171855934577542059451052515002 : ((((p1 ∨ p5) → ((p4 → (True → (True → ((False ∨ p1) → p5)))) ∧ p2)) → p2) ∨ ((False ∨ False) ∨ ((False ∧ p4) → (p1 ∧ (p4 ∧ p2))))) := by
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
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622058647811404446236070983842 : ((((p2 ∧ ((False ∨ ((True ∧ (((p1 → (p3 ∨ True)) ∧ p4) ∧ (((False → p3) ∧ p2) ∨ ((p4 ∨ p1) ∧ p2)))) → False)) → p4)) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245152604115020809872442143411 : ((p2 ∧ True) ∨ (p5 → (((((p4 ∨ p1) ∧ (((p1 → (True ∧ p5)) → (p1 ∨ (p1 ∨ p3))) → p4)) → p2) ∨ (False ∧ p4)) ∨ (p2 → p2)))) := by
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
theorem thm_5_vars_685120487403715410627761600755 : ((((p2 ∨ ((((p3 ∨ p2) → (p1 ∨ p5)) ∨ p5) ∧ (((False ∧ p5) → (True → p1)) ∨ p5))) ∨ (((p5 ∨ (p2 ∧ False)) ∧ p4) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248046526271346614640442987492 : ((p1 ∨ p5) ∨ ((p3 → (p2 ∧ False)) → ((((p2 → p1) → (p1 → (True ∧ (p4 ∨ p1)))) → p2) ∨ (((p3 → (p4 ∧ p1)) ∨ p4) → True)))) := by
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
theorem thm_5_vars_148681711409414599852413617122 : (((((p3 ∧ p2) ∨ p3) ∧ (p3 → (p1 → False))) ∨ (p1 → ((((p3 ∨ p2) ∨ True) → p2) ∨ (p4 → p1)))) ∨ (((p3 ∨ p1) → p4) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180992637222123097287714881141 : (((p3 ∧ p1) ∨ ((((p1 ∨ p4) → (p5 ∧ p1)) ∧ (p1 ∧ p1)) ∧ p1)) → ((p1 → p4) → (((p1 ∧ (p4 → p5)) ∧ (p4 → False)) ∨ p1))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53707350299562896530814180856 : (((p1 ∨ ((p1 ∧ p4) ∧ ((False → p3) → (p4 → p2)))) ∧ ((p2 ∧ p2) ∨ ((True → (p4 → (p1 ∨ p4))) ∧ (p1 ∨ (p4 ∨ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337651538440992662418984114408 : (p1 → (((((p3 ∧ p2) ∨ False) ∧ ((False → (((p1 → p3) ∨ p5) ∧ p1)) → (p3 ∧ p5))) ∨ True) ∨ (((p3 → p3) → (p2 ∧ False)) ∧ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40680696068731285398849964198 : ((((((p1 ∧ (((p4 ∧ (True ∧ (((p2 → p5) ∧ (True ∨ p2)) ∧ p1))) ∧ True) → p1)) ∨ p4) → (p4 ∧ (p1 ∧ p4))) → False) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720004722896640361497460242302 : ((((((p5 → p3) ∧ p2) ∧ p1) → (True ∧ ((False ∧ (p2 → True)) ∧ ((((p4 → ((p2 ∧ p5) ∨ True)) ∧ p5) ∨ (True ∨ p2)) ∧ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321232148261553766148203086298 : (p4 ∨ (p4 ∨ (((p2 ∨ ((p3 → ((((p3 ∧ (p2 ∨ False)) ∨ ((p5 ∨ p1) ∧ (p5 → p1))) → p2) ∧ p5)) → p1)) ∨ (p1 → p4)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669991315910733929853064933007 : (((((p5 ∨ ((((p5 ∨ p1) ∨ (p2 ∨ p2)) ∨ False) ∨ p1)) → ((p5 ∨ False) → ((p4 ∨ p1) ∧ (p5 ∧ p3)))) ∨ ((p4 ∧ p3) ∨ True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_892317582006394842523420171704 : (((((((((True ∨ False) ∨ p1) ∨ ((p1 ∧ p5) ∧ p1)) → (((p3 ∧ p2) → False) ∧ (p5 → p1))) ∨ p4) → False) ∧ ((True ∨ p3) ∧ p4)) → False) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : (((((True ∨ False) ∨ p1) ∨ ((p1 ∧ p5) ∧ p1)) → (((p3 ∧ p2) → False) ∧ (p5 → p1))) ∨ p4) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h7
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h10 : (((((True ∨ False) ∨ p1) ∨ ((p1 ∧ p5) ∧ p1)) → (((p3 ∧ p2) → False) ∧ (p5 → p1))) ∨ p4) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h11 := h2 h10
    -- False on the left can always be used.
    apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179345707525128099879840232972 : ((p1 ∨ (p1 ∨ (True ∧ (((True → (p5 ∧ p4)) → False) ∨ (p5 → p5))))) ∨ ((p5 → ((p1 ∨ p2) ∨ ((p3 ∧ p5) ∨ (p4 → p5)))) → p4)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352460148938451478546470825730 : (p4 → (((p1 ∧ p1) → p2) → (False ∨ (((((((False ∧ (p3 ∧ p1)) ∨ (p5 ∨ p5)) ∧ (p1 → p1)) ∧ (False ∧ p1)) ∧ p3) ∨ p2) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150019467169812694247634795944 : ((p5 ∨ ((((True → p2) ∨ ((True → (True ∧ (p5 → False))) ∨ True)) ∧ p5) → ((p5 ∧ (p2 ∧ False)) ∨ True))) ∨ (p3 ∧ ((p2 ∧ p3) ∧ p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_686311231063331200310691056370 : ((((((p5 ∨ (False → True)) ∨ (p3 ∨ p3)) ∧ (((p2 ∨ ((True ∧ False) → p4)) → p5) ∧ p1)) → ((((p2 ∧ p4) → p3) ∧ True) ∨ p5)) ∨ p4) ∧ True) := by
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
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h3.left
      let h7 := h3.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h3.left
      let h10 := h3.right
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h11 : (p2 ∨ ((True ∧ False) → p4)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h12
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- False on the left can always be used.
        apply False.elim h14
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h15 := h9 h11
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h15
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h3.left
      let h19 := h3.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h20
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- One of the premise coincides with the conclusion.
      exact h17
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h23 =>
      -- Conjunctions on the left can always be decomposed.
      let h24 := h3.left
      let h25 := h3.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h26
      -- Conjunctions on the left can always be decomposed.
      let h27 := h26.left
      let h28 := h26.right
      -- One of the premise coincides with the conclusion.
      exact h23
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149102702494911421856247259503 : (((True → (p1 ∨ p5)) → (((p5 ∨ p3) ∧ ((p3 ∨ (p1 ∧ ((False ∧ p2) ∨ (p1 ∧ p1)))) → p1)) ∨ p4)) ∨ (True ∨ ((p4 → False) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186474841485704648715555376991 : (((((p2 → False) → (p1 ∧ p3)) → (p3 ∧ False)) ∧ (p3 ∧ p1)) → (p3 ∧ ((p2 → ((p1 ∧ p5) ∧ False)) ∨ ((p2 → p1) ∧ (False ∨ p1))))) := by
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
  exact h4
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h10
  -- One of the premise coincides with the conclusion.
  exact h9
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662337833585925383249891945984 : ((((((True → False) ∨ ((p2 ∨ (p2 ∧ p1)) ∧ False)) ∧ (p2 → (p4 ∧ ((p4 ∧ (p1 ∧ (p2 ∧ (p1 → True)))) ∧ p1)))) → (p3 ∧ False)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- False on the left can always be used.
      apply False.elim h9
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- False on the left can always be used.
      apply False.elim h9
  -- Conjunctions on the left can always be decomposed.
  let h14 := h1.left
  let h15 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h14
  case inl h16 =>
    -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
    have h17 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h16, we can now drive its conclusion.
    let h18 := h16 h17
    -- False on the left can always be used.
    apply False.elim h18
  case inr h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h19.left
    let h21 := h19.right
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h22 =>
      -- False on the left can always be used.
      apply False.elim h21
    case inr h23 =>
      -- Conjunctions on the left can always be decomposed.
      let h24 := h23.left
      let h25 := h23.right
      -- False on the left can always be used.
      apply False.elim h21
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118342993304863340988477460406 : ((p2 ∨ (((p5 ∨ p3) → ((((False → (((True ∨ p3) ∧ (p1 ∧ p2)) → p1)) → p2) ∧ ((p5 → p2) ∨ True)) → p5)) ∨ True)) ∨ (True ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65850698320513801469242158689 : ((p4 ∨ (((p5 ∨ True) ∨ p5) → (((p5 → (((p2 → False) ∧ p2) ∨ ((((p1 → p1) ∨ (p3 ∧ p2)) ∨ True) ∨ p5))) ∧ True) ∨ False))) ∨ p4) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h4
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h8
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42283093889012806788598595914 : (((p1 ∧ (p1 ∨ (p5 ∨ (p4 ∧ (p5 ∨ (False ∨ ((p5 ∧ True) ∧ ((p3 → False) ∧ ((p2 → (True ∨ (False ∧ p4))) → p4))))))))) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165301788605118870387023712816 : ((((p4 ∨ p2) → ((p4 → ((True ∧ True) ∧ ((p3 → p1) → False))) ∨ p4)) → (p1 → p2)) ∨ ((False → (True ∧ False)) ∨ (p3 ∨ (True ∨ p3)))) := by
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
theorem thm_5_vars_38738108331172485512350449775 : ((((p3 → (((False → True) → True) ∧ p4)) → ((True ∧ ((((p5 ∨ (p4 ∨ p4)) ∧ p1) → (p5 → True)) ∨ p3)) → (p2 → False))) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343555015702849598252191558041 : (p2 → ((p3 ∨ True) → ((((p2 ∧ (p4 ∨ (((p5 → (p1 ∧ p1)) → p4) ∨ ((p3 ∨ (p4 → p3)) ∧ True)))) ∧ (p1 → p3)) → p5) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_599045282692419034163731949035 : (((((p5 ∨ True) ∧ ((p2 ∨ (p3 ∨ (p1 ∨ p4))) ∧ ((False ∨ (p5 → ((p5 → (p2 ∨ p3)) ∨ p2))) → (False ∨ (True → False))))) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208741171228728466109425965475 : ((p1 ∧ (p4 ∧ (True ∧ (True → p4)))) → (((True ∧ p3) ∨ (False ∨ ((True → (True → p2)) → (p2 → (p1 → (False ∨ p5)))))) ∨ (True ∧ True))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56455311936531699662481924634 : ((((p2 → p2) ∨ (p3 → p5)) → (((p5 ∧ (False ∨ (p1 ∧ (p4 ∨ ((((True → True) ∧ False) ∧ p5) → (False ∧ False)))))) ∧ p2) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_128481122898856651039306370107 : ((p5 → ((p1 ∨ (p2 ∨ (((False ∨ ((p5 → True) ∨ p5)) → ((p2 → True) ∧ p5)) ∨ False))) ∧ ((p4 ∧ (p1 → True)) ∧ p3))) → (p5 → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347130110592265209390970809169 : (p3 → (((p5 → (False ∨ ((False → (((p2 → False) ∨ p2) ∨ p2)) → False))) ∨ p3) → (p1 → (p1 → (((p5 ∨ p2) ∧ (p5 ∧ p3)) ∨ p1))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264660733657404601981569481246 : (True ∧ ((p3 → (p3 ∧ p4)) → ((p2 ∨ False) → (p1 ∨ (((p2 → p3) → (p1 ∨ p1)) ∨ (p5 ∨ (((p1 ∨ True) → p3) ∨ (p1 ∨ p2)))))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310114572104884052336315331748 : (p2 ∨ ((((p3 ∨ True) ∧ ((p3 → False) ∨ ((p5 → (p5 ∨ p2)) → p2))) ∨ True) ∨ (p2 → (((p3 ∧ True) ∧ p5) → (p3 ∧ (p4 ∨ p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158558377031880096801222605269 : ((True ∧ (((True → (((False ∨ p1) ∧ (True ∧ p2)) ∨ (((False → p5) ∨ p2) → p3))) → False) ∨ p5)) ∨ (p2 ∨ ((p3 → (p2 ∧ p5)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_483323995082491397433056175256 : ((((p4 → (p5 ∨ (False ∧ (True ∨ (p5 ∧ p1))))) → ((p3 ∨ ((p3 ∨ p1) ∧ ((p2 ∧ True) → (p1 ∧ (True ∧ (p5 ∧ p2)))))) ∨ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259119606850214468449754567707 : ((True → p5) → (p4 → (((p3 ∨ (True → (p3 → ((p5 → ((False → (True ∨ p2)) ∧ False)) → (p2 ∨ False))))) ∧ (p2 ∨ p5)) ∧ (p4 → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : p5 := by
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h8 := h1 h7
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h9 := h5 h6
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- False on the left can always be used.
  apply False.elim h10
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h11 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h12 := h1 h11
  -- One of the premise coincides with the conclusion.
  exact h12
  -- Implications on the right can always be decomposed.
  intro h13
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_786355029036798664496659233026 : (((p4 ∨ (((p2 ∨ (p3 ∧ False)) ∨ ((p2 ∨ (p2 → False)) → ((True ∨ (p3 ∧ p3)) ∧ p2))) ∨ ((((p4 → p2) ∧ False) → p3) ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683466262168078573394472450027 : ((((p2 → ((p1 ∧ (p3 ∨ ((p2 ∨ True) → p3))) ∨ ((False ∧ (False ∧ p3)) ∨ (p2 → p3)))) ∧ (((p4 ∨ (p5 ∧ p2)) → p5) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669134507008795622301916418443 : (((((((True → ((False ∨ p1) ∨ p1)) → (p4 → p4)) ∧ ((True → (p2 ∨ p2)) ∧ (p1 ∨ (p4 → p5)))) → False) ∨ (p3 ∨ (True → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669325244348461296533361205229 : (((((((False ∧ ((p2 → p4) ∨ p5)) ∨ (((p4 → False) ∨ p2) ∨ p3)) ∨ ((True → p4) ∨ p2)) ∧ (p4 ∨ p3)) ∨ (False → (True → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41962567558586327315876090411 : ((((p5 ∧ p1) ∧ ((False ∨ (((p3 → p2) ∧ (p1 ∧ p5)) ∨ ((p5 ∨ ((p5 ∧ (p4 ∧ p2)) ∧ False)) ∧ (True ∨ p3)))) ∨ p5)) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659885529649067936757890149033 : (((((p5 → ((True ∧ p1) ∧ ((p3 ∨ (p5 → (((False ∨ (p2 ∧ p4)) ∧ p5) → p1))) ∨ ((True ∨ p3) ∨ p2)))) ∧ p4) → (p1 → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347628766645809472234104149810 : (p3 → ((True → ((True ∧ p4) ∨ p4)) ∨ ((False ∧ ((True ∧ ((p3 → True) → (((p1 → False) ∧ p4) ∨ True))) → (p5 ∧ p4))) ∨ (p4 ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263423459803334506295581331880 : (True ∧ ((p1 ∨ (p2 ∧ ((((True ∨ (p3 ∨ (p4 ∨ p5))) → (((p4 ∧ (p2 → p4)) ∨ p1) → p4)) ∨ p4) → p1))) ∨ (True ∨ (p1 ∧ p5)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54030756000364194381315080125 : ((((((p2 → False) ∧ p2) ∧ (True ∨ p4)) ∨ (p3 → p2)) → ((((((True → p3) ∨ p3) ∧ p1) → (False ∧ p5)) ∨ (p1 ∨ p3)) ∨ True)) ∨ p1) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
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
theorem thm_5_vars_326981961292324767883708788730 : (True → (((False ∨ ((p5 ∨ p1) ∨ (True ∧ ((True → p5) ∧ (p4 ∧ ((p2 ∧ (p3 → False)) ∧ (p1 ∨ False))))))) ∨ (p5 ∨ (False ∨ p3))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151257861420134799926165470320 : ((((False → p1) → (p2 ∧ (((p4 → ((p3 ∨ (False → p2)) ∧ (True ∨ (p3 ∨ True)))) ∨ p1) ∨ p1))) → p5) → (p1 ∨ ((p3 → p1) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_561365340000791634304419485671 : (((p4 ∨ (p3 → ((((p5 → ((((False ∨ True) ∧ (True → p3)) ∧ p4) ∨ p2)) ∧ ((p5 → (False → p5)) ∨ (p4 ∨ p4))) → p5) ∨ p3))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_120000119709944968856566357664 : ((((((p4 ∧ ((p4 ∧ ((True → p5) → p4)) ∨ (False ∧ p5))) ∨ p5) ∨ False) → (p2 ∧ (True ∨ (p1 ∧ (p4 ∧ p1))))) ∧ p1) → (p5 ∨ True)) := by
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
theorem thm_5_vars_161497975903786885064453003202 : ((p4 ∧ ((False ∨ ((((p3 → (((p5 ∧ p5) ∨ p1) ∧ (p4 ∧ p3))) ∨ p4) ∧ False) ∨ True)) → False)) → (p2 → (False ∨ ((p5 ∨ p3) ∧ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : (False ∨ ((((p3 → (((p5 ∧ p5) ∨ p1) ∧ (p4 ∧ p3))) ∨ p4) ∧ False) ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_605858166581515304291059041243 : ((((p5 → ((True ∧ ((((p3 ∧ (((p2 → (p5 ∧ ((p1 ∨ False) ∨ p3))) ∨ (True → p2)) → p4)) ∨ p2) ∧ p1) ∨ p4)) ∧ False)) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124907581241353474191354692462 : (((((p5 ∧ p1) → p3) ∨ True) → ((((p5 → p4) → True) → p1) → ((p4 ∨ (p5 → (False → p2))) ∨ (p4 → (False → p4))))) → (p2 ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68369269102986116509209079233 : ((p3 → ((p4 ∧ ((p5 ∨ (False ∨ p4)) ∧ p3)) ∨ (((((True → (True ∨ p2)) ∨ p5) → p5) ∨ False) ∧ ((p2 ∨ (p3 ∨ p2)) ∨ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113133419847697120471262027953 : (((p2 → ((p4 ∧ (p4 ∨ ((p2 ∨ (p1 → ((p1 ∨ False) ∧ p4))) ∧ (((p1 ∨ p3) → (p2 → p5)) → p1)))) ∨ p5)) → p2) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311926465151644168918520027796 : (p2 ∨ (p3 ∨ (((((p1 ∨ p3) ∧ p5) ∨ (p2 ∧ (p4 ∨ p3))) → ((p5 ∨ (False ∨ False)) ∧ (((p2 ∨ p5) → p5) ∧ (p2 → p2)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



