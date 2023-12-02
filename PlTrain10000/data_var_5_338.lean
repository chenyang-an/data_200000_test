variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_782445130311296226470958313891 : (((p3 ∨ ((((p4 → (p2 → (p3 ∧ (p2 → p1)))) ∧ ((((p5 ∧ p4) ∨ False) ∧ p2) ∧ p1)) ∧ ((p4 ∨ False) ∧ (p5 ∧ True))) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225974682822446609011020281864 : (((p3 ∧ p2) ∨ p2) ∨ (p3 ∨ ((True → (p4 → ((p2 ∨ p1) ∧ (p2 ∨ False)))) ∨ (((((False ∧ p5) → p2) ∨ False) → (True ∧ False)) → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((False ∧ p5) → p2) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47515029587036959414252020771 : (((p2 ∨ (p5 ∨ (((((p4 ∧ (p2 ∧ True)) ∨ ((p3 → p3) ∧ (False ∧ (False ∨ False)))) ∨ p4) ∨ False) ∨ (p3 ∨ True)))) ∨ (p4 ∧ p4)) ∨ p3) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208494968843167402821146985306 : (((False ∧ p4) → ((p2 ∧ p1) → p1)) → (p5 ∨ (((False → (False ∧ p4)) → ((((p2 ∧ p2) ∨ p1) ∨ True) → (False ∧ (False ∧ p2)))) → False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (False → (False ∧ p4)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h4
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : (((p2 ∧ p2) ∨ p1) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164515969516078362723261210159 : (((((p4 ∧ (p3 ∨ ((False ∧ (p1 → (p2 ∨ p3))) → p4))) → p3) ∨ (True → True)) ∧ p3) ∨ ((True ∧ (True ∨ p3)) ∨ (p2 → (p2 ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258980140355808956348529798176 : ((True → p3) → ((False ∨ p2) ∨ ((((((p2 → (p3 ∧ p3)) ∨ True) → p4) → (p3 → p1)) → (False ∧ (p5 ∨ p1))) ∨ (p3 → (p5 ∨ True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358228206450865195389764882502 : (p5 → (p4 ∨ ((((p2 ∨ p2) ∧ ((True ∧ ((False → (True ∧ p3)) → True)) ∨ p4)) ∧ ((p3 ∧ ((p3 → p2) → p1)) → p4)) ∨ (p5 → p5)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185769695193278828902822216298 : ((p4 → ((p1 ∨ (p1 ∧ (p2 ∧ p1))) ∨ (p2 ∨ (p1 ∨ True)))) ∨ ((p5 ∧ ((p2 → p5) ∧ p1)) → (p3 ∨ ((p2 ∧ (p4 ∨ p2)) → p3)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191087055344818844008589896691 : ((((p1 ∧ p5) ∨ p1) ∧ (p2 ∧ ((p4 ∧ p5) ∧ p3))) ∨ (p3 → ((((((p4 → p2) ∧ p3) ∧ p5) ∨ True) ∨ (False ∧ (p2 ∨ True))) ∨ p5))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_681734547402590373227137363314 : (((((((False → True) ∨ (p1 ∧ (p2 ∨ ((False ∨ (p5 ∧ (False ∨ p5))) ∨ True)))) ∧ p4) ∧ p5) ∧ (p2 ∧ ((p5 ∨ p4) → (p4 ∨ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699542554501250672024808909816 : (((((p5 ∨ (((p5 → (p2 → (p4 → p2))) ∧ p3) ∧ p2)) ∨ p4) → ((((p4 ∨ p2) ∨ p4) ∧ (p2 ∨ (p1 ∨ (p5 ∨ False)))) ∨ True)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h7 := h5.left
      let h8 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164153017389339019698026557207 : ((p4 ∨ (((((p4 ∧ p2) ∨ p1) ∧ ((p3 ∨ p4) ∨ p2)) → ((p4 ∧ p5) → False)) ∨ True)) ∧ ((p3 → p4) ∨ (True ∨ ((True → False) → p5)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118845966722015616120914483306 : ((True → (((((p2 → p2) ∨ (p4 ∧ ((p2 ∧ p1) ∧ (True ∨ p4)))) ∧ p1) ∨ (p3 ∨ p3)) ∨ (p1 ∨ (p4 ∨ (p5 → p5))))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138296268200818425267173280780 : ((p3 → ((((((p1 ∧ (p5 ∧ p3)) → (p3 → p4)) → (False → p3)) → (p2 → p1)) ∧ p4) ∨ ((p2 ∧ False) ∨ True))) ∨ (True ∨ (p1 ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51612914202214735785977421230 : ((((((p3 ∨ ((False → p5) ∧ (p4 → (p5 → p4)))) ∧ (p5 → p3)) → False) ∧ p3) ∧ ((((p3 ∨ p4) ∨ (p1 ∨ p1)) → True) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46421264451983288205125030523 : ((((p1 ∧ ((p1 ∨ (p5 → p3)) ∧ True)) ∧ (((p2 ∧ (p3 ∨ (True ∨ p2))) ∧ ((True ∨ p5) → False)) ∨ (p3 ∨ False))) ∧ (p5 → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263552059072798856562964168880 : (True ∧ ((((((p3 ∧ p4) → (((False ∧ p4) ∨ False) ∧ ((False → p1) ∧ False))) ∧ True) ∧ (False ∨ p5)) ∨ True) ∨ (((p2 ∧ True) → p2) ∨ p3))) := by
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
theorem thm_5_vars_157076119797003721806337452546 : (((p2 ∨ ((p3 → ((p3 ∨ p2) → (p4 → (p5 ∧ ((p3 → p5) → (p2 ∨ p2)))))) → p5)) ∨ p1) ∨ (((p2 ∨ p4) → p2) → (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258413137353200987465502853306 : ((p5 ∨ p1) → (((((p2 ∨ p1) ∨ True) ∧ False) ∨ (p3 ∧ (p1 ∨ (((p5 ∧ (True → (p3 ∨ True))) ∨ (p3 → p5)) ∧ p3)))) → (False ∨ p3))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- False on the left can always be used.
        apply False.elim h5
      case inr h8 =>
        -- False on the left can always be used.
        apply False.elim h5
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h5
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h11
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h19 =>
        -- Conjunctions on the left can always be decomposed.
        let h20 := h19.left
        let h21 := h19.right
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h22 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h18
        case inr h23 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h18
      case inr h24 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h25 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h18
        case inr h26 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233804849396071071813231871507 : ((p3 ∨ (p2 → True)) → ((((((((p1 → p4) ∧ (p5 ∧ True)) ∧ p1) ∨ (p4 → p5)) ∧ True) ∧ (p5 → p2)) ∧ (True → p3)) → (p4 → p4))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h11.left
    let h14 := h11.right
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h17 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h18 =>
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h19 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h20 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h21 =>
      -- One of the premise coincides with the conclusion.
      exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45998636465772738162813553204 : (((((p2 ∧ (((((False ∨ (False → False)) ∨ p4) ∧ ((p3 ∨ p4) ∧ p3)) → p1) → (p1 → False))) ∨ (p5 ∨ p4)) ∧ p3) ∧ (p1 ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_735677344625266887982305046670 : ((((p5 ∨ p2) ∧ (((((True ∨ p3) ∧ (False ∨ (p3 ∧ (p1 ∧ (False ∨ p1))))) → p2) ∧ (False ∧ (p3 ∨ (False ∨ p5)))) ∨ (p3 ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39557376280240134086296369515 : (((p1 ∨ (((((True ∧ (p2 ∧ (((p4 ∨ (p2 ∨ (p2 ∨ (p5 ∨ (p5 → False))))) ∧ p4) ∨ p2))) ∧ True) ∧ p5) → p2) → p2)) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115459208985189970036570474317 : ((((False → p3) → (p2 ∨ ((p3 ∨ p3) ∨ p5))) ∨ ((((True → (p4 ∧ True)) ∨ (p5 → p3)) → False) → (True ∨ (True ∨ p2)))) ∨ (p1 → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783217926805199365084020457902 : (((p3 ∨ (((True → (p4 → (((p3 → p4) → p3) ∨ ((p1 → True) → ((p3 ∧ p4) → True))))) → (p3 ∧ False)) → ((p3 → True) ∧ False))) ∨ p3) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (True → (p4 → (((p3 → p4) → p3) ∨ ((p1 → True) → ((p3 ∧ p4) → True))))) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h3
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147881155724321782669442405660 : (((p5 → (True ∨ ((p1 → (((p3 ∨ ((False ∧ (True ∨ (False ∨ True))) → p4)) ∧ p5) → p5)) → True))) → p4) ∨ ((p5 → p5) → (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_791524316703393621723589160415 : (((True → ((p3 → ((p4 ∨ ((p2 → (p5 ∧ ((p4 ∨ (((p1 ∧ p4) → (False → p5)) ∨ p1)) → (p3 → p2)))) ∧ p1)) ∧ False)) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307413192887312830916157464033 : (p1 ∨ (p4 ∨ (p2 → ((p5 ∨ ((p4 ∧ (p4 ∧ p2)) ∧ (((p1 ∧ p2) ∨ (((((p3 ∨ p2) ∧ p2) → p4) ∨ False) → p4)) ∨ p2))) ∨ p2)))) := by
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
theorem thm_5_vars_117437735658309985538848816325 : ((p1 ∧ (((p2 → p4) ∨ ((p3 → (p1 ∧ p5)) → (p4 ∨ p3))) ∧ (p3 ∧ (p1 → ((p1 ∨ (False ∧ (p2 → p3))) → p2))))) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_597983745762436916998652608085 : (((((p4 ∧ (p3 ∧ p3)) ∧ (p1 ∧ (((p4 → (((False ∧ ((p2 ∨ p5) → (p2 ∨ False))) → p4) → (False → True))) ∨ True) ∧ p5))) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55682787596026652985097679904 : (((((p3 ∧ p2) ∨ False) ∨ p1) ∧ (True ∧ ((((p2 ∨ (p4 ∨ (p5 ∧ p4))) ∨ p2) ∧ ((False ∨ p5) ∧ (False ∨ (p2 → p4)))) ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_83810155235427586479204869608 : ((((((p1 ∧ p5) ∨ (p2 → (p4 ∨ ((True ∧ p5) ∨ p4)))) ∧ p2) ∨ (p4 → (p2 → p4))) → ((((p2 → p2) ∨ p1) ∧ False) ∨ False)) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p1 ∧ p5) ∨ (p2 → (p4 ∨ ((True ∧ p5) ∨ p4)))) ∧ p2) ∨ (p4 → (p2 → p4))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
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
      apply False.elim h8
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h8
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45991147702164480188300744894 : ((((((p1 ∧ ((p2 → (True → ((p4 → p1) ∧ True))) ∨ p2)) ∨ (((p4 ∧ p5) ∧ p3) ∧ (True ∧ p4))) → False) ∧ p1) ∧ (False ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309356980090447061729673246289 : (p2 ∨ ((((p2 ∨ (p2 → ((p1 → p5) → p1))) ∧ p3) ∨ (((p3 → True) ∨ False) → (((False ∧ (p2 → p1)) → p1) ∨ p4))) ∨ (p2 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173770924344087760959244973858 : ((((True ∨ (p1 → p5)) → (((p3 ∧ (p3 → p3)) ∨ True) → (p5 ∧ p4))) ∨ p5) → (p4 ∨ (p3 ∨ ((p3 ∧ (p4 ∧ (p2 ∧ False))) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312155871032209211861166912677 : (p2 ∨ (True → (True → (p5 ∨ ((False → ((False → p2) → p1)) → (((False ∨ (p2 ∨ (True → (False → (p3 ∧ p2))))) ∧ (p1 ∨ True)) ∨ False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h5
  -- False on the left can always be used.
  apply False.elim h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50177878798511241207489749607 : ((((((True ∧ (p5 ∨ (((False ∨ p1) ∨ ((p4 ∧ False) ∨ False)) ∨ p3))) ∨ p5) ∧ (p5 ∧ p5)) ∧ p2) ∨ ((False → p5) ∨ (p3 ∧ True))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_641942602482821947107513822837 : (((((p4 → False) → (((((p1 ∨ True) ∨ (((True ∧ (p5 ∧ p3)) ∧ False) ∨ ((p3 → p4) → True))) → (p3 → p2)) → p3) → p4)) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65395374147669528566479123087 : ((p3 ∨ (((((False → p4) → False) ∧ True) → True) → (p2 ∧ (((False ∧ True) → ((p5 ∧ p5) → (((p2 ∨ p2) ∧ False) → p1))) ∧ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205359619822483755554365064069 : ((((True → p4) ∧ True) → (p1 ∨ p5)) ∨ ((False ∧ (p5 → (p4 ∨ (p2 ∧ ((p1 ∨ ((p1 ∧ p2) → p5)) ∧ True))))) ∨ ((p3 ∨ p3) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_554428439561413681384043418922 : (((p2 ∨ (((True ∨ p4) ∧ p3) → ((((p5 ∧ p4) ∨ p2) ∨ (p4 ∨ p3)) ∨ ((p2 ∧ (False → ((p3 ∧ False) ∧ (p5 ∧ p2)))) ∨ p2)))) ∧ True) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_84018519315019067433348321156 : ((((((((True ∨ False) ∧ (True ∧ ((False ∧ p1) → True))) ∧ True) → False) → p1) → False) ∧ (((p1 ∧ (p1 ∨ p5)) ∧ p1) → (p2 → p1))) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (((((True ∨ False) ∧ (True ∧ ((False ∧ p1) → True))) ∧ True) → False) → p1) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : (((True ∨ False) ∧ (True ∧ ((False ∧ p1) → True))) ∧ True) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h7
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h6
    -- False on the left can always be used.
    apply False.elim h8
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h4
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196835770062748666212320501432 : (((p4 ∧ ((True ∨ (p5 ∨ True)) ∧ p4)) ∧ p5) ∨ ((p3 ∨ p1) ∨ ((p5 ∨ ((True ∨ (p3 → ((p2 ∧ p1) ∨ (p3 ∧ p2)))) ∨ p2)) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46359036882598955941195340886 : ((((((p1 ∨ ((True → p4) ∨ (p5 ∨ True))) ∧ p4) ∨ (p5 ∧ False)) ∧ ((p1 ∨ p1) ∨ ((p5 ∨ (p3 ∨ p4)) → p5))) ∧ (p2 → True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246543379379701904275150078233 : ((p5 ∧ p1) ∨ (p4 ∨ (False ∨ (True ∧ ((p2 ∧ True) ∨ (((p5 → True) → False) → ((((True ∧ p5) ∨ False) ∧ p1) → (p1 → (True ∧ p4))))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h9 : (p5 → True) := by
      -- Implications on the right can always be decomposed.
      intro h10
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h11 := h1 h9
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252309176717993334293451450490 : ((p4 → p5) ∨ (False ∨ (((p1 ∧ (p4 → p2)) ∧ ((((p5 ∧ p3) ∨ (p4 ∧ False)) → p4) ∨ p1)) ∨ ((False ∧ ((p2 ∧ True) ∨ p4)) → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_242993773840170676632720462539 : ((p4 → True) ∧ ((((True → False) → (((p3 ∨ False) ∨ (p5 ∨ p2)) ∨ True)) ∧ (p1 ∨ (False → p3))) ∨ (((p2 → (p4 → p3)) ∨ p5) ∨ p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216743981326115817792827416846 : ((((p5 ∨ p3) → p5) ∧ p1) → ((p3 ∨ ((((p4 → (((p5 ∨ p3) ∨ p2) → (p5 → (p5 ∨ p1)))) → (p5 ∧ p2)) ∨ True) ∧ True)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_344315522022034871877096717531 : (p2 → (p3 ∨ ((p2 ∨ ((p4 → p1) → p5)) → (p3 ∨ (((False → (True → (((p1 → False) ∧ p5) → p1))) ∧ (False ∨ p2)) → (p5 → p5)))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- Implications on the right can always be decomposed.
    intro h12
    -- Conjunctions on the left can always be decomposed.
    let h13 := h11.left
    let h14 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- One of the premise coincides with the conclusion.
      exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323551849196203997735422178006 : (p5 ∨ (((((((p5 → (p3 ∧ p4)) ∧ p3) ∧ True) ∧ (((p4 ∧ p4) → p4) → (p2 ∧ True))) ∧ p2) ∧ (p1 ∧ p1)) → ((True ∧ p3) ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h3.left
  let h13 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h11
  -- Conjunctions on the left can always be decomposed.
  let h14 := h1.left
  let h15 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h16 := h14.left
  let h17 := h14.right
  -- Conjunctions on the left can always be decomposed.
  let h18 := h16.left
  let h19 := h16.right
  -- Conjunctions on the left can always be decomposed.
  let h20 := h18.left
  let h21 := h18.right
  -- Conjunctions on the left can always be decomposed.
  let h22 := h20.left
  let h23 := h20.right
  -- Conjunctions on the left can always be decomposed.
  let h24 := h15.left
  let h25 := h15.right
  -- One of the premise coincides with the conclusion.
  exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167974779668487713523992191564 : ((((p1 ∧ (p4 ∧ (False → p1))) ∧ p4) ∧ ((p5 ∧ True) → ((p1 → (p3 ∧ p4)) ∨ True))) → ((((p2 → (p3 ∨ p1)) ∧ p3) ∧ False) ∨ True)) := by
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
  let h8 := h7.left
  let h9 := h7.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157891052169284162727053223202 : (((p3 ∨ (p1 ∨ ((p2 → p1) → ((p4 ∧ p2) → p5)))) ∨ (p1 ∨ (p2 ∨ (p2 ∨ (True ∨ False))))) ∨ ((p1 → True) ∨ (p4 ∧ (p1 ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166378006470579316652709245268 : ((False ∨ ((((p4 ∧ (False ∧ (p5 ∧ p2))) ∨ True) ∨ ((p3 → p1) ∨ (p3 ∧ p4))) ∨ p2)) ∨ ((p3 ∨ (False ∨ ((p5 ∧ p3) ∨ False))) ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133624914227828615331505617369 : (((((p2 ∧ p2) ∧ (((((p3 ∧ True) ∧ ((p4 ∨ (p1 ∨ p4)) → p3)) → p5) ∨ (p2 ∧ p1)) ∧ p1)) → p4) ∧ p1) ∨ (False ∨ (True → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50238330997743632385904203921 : ((((((((False → (p3 ∧ (p4 → False))) → p1) ∧ False) ∧ ((p2 ∧ p3) → (p2 ∧ p2))) → p1) → p3) ∨ ((p1 → (p2 ∧ True)) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232970293447339506386533689125 : ((p3 ∧ (False → p3)) → ((p3 ∧ ((p5 ∨ True) ∧ ((p1 ∧ (p4 → ((True → (p5 ∨ p1)) ∨ p3))) → p4))) → (((True ∨ p4) ∧ p1) → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h2.left
    let h8 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h1.left
      let h13 := h1.right
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h14 : (p1 ∧ (p4 → ((True → (p5 ∨ p1)) ∨ p3))) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h5
        -- Implications on the right can always be decomposed.
        intro h15
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h12
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h16 := h10 h14
      -- One of the premise coincides with the conclusion.
      exact h16
    case inr h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h1.left
      let h19 := h1.right
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h20 : (p1 ∧ (p4 → ((True → (p5 ∨ p1)) ∨ p3))) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h5
        -- Implications on the right can always be decomposed.
        intro h21
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h18
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h22 := h10 h20
      -- One of the premise coincides with the conclusion.
      exact h22
  case inr h23 =>
    -- Conjunctions on the left can always be decomposed.
    let h24 := h2.left
    let h25 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h26 := h25.left
    let h27 := h25.right
    -- Disjunctions on the left can always be decomposed.
    cases h26
    case inl h28 =>
      -- Conjunctions on the left can always be decomposed.
      let h29 := h1.left
      let h30 := h1.right
      -- One of the premise coincides with the conclusion.
      exact h23
    case inr h31 =>
      -- Conjunctions on the left can always be decomposed.
      let h32 := h1.left
      let h33 := h1.right
      -- One of the premise coincides with the conclusion.
      exact h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3287721032645523705591819172 : ((p5 → p1) ∨ ((p4 → False) ∨ (((False ∧ p1) ∧ (p2 ∧ (p5 ∧ (p3 ∧ ((p3 → (p2 ∧ (p5 ∧ (False ∨ p4)))) → p1))))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328442874579258711938202639256 : (True → (((((p2 ∧ p3) ∧ p3) ∨ ((p5 → p3) ∨ (False → (False ∨ ((p3 ∧ p2) → False))))) ∨ False) → (((False ∧ p3) ∨ p3) ∨ (False → True)))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h7 := h5.left
      let h8 := h5.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h13
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h14 =>
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315694877393608717777993713371 : (p3 ∨ ((p2 ∨ p1) ∨ ((((p3 ∧ (p5 ∨ p2)) ∧ p2) → (False ∨ (False ∨ (p4 → ((p2 ∧ p4) → p3))))) ∨ ((p5 ∧ (p5 ∧ p2)) ∧ p3)))) := by
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
  cases h5
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- Implications on the right can always be decomposed.
    intro h13
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_681549597547515901423893893912 : ((((False → (((p4 ∧ ((p2 ∨ (p4 ∨ (p4 ∨ True))) → p1)) → p5) ∧ (p5 → (p1 ∧ (p5 → False))))) → (((p5 → p4) → p3) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248729682065191886617991595110 : ((p3 ∨ p2) ∨ (p4 ∨ (p3 ∨ (p5 ∨ (True → (((((p3 ∨ p5) ∧ (((True ∧ p5) ∨ p1) ∧ ((True → p2) ∨ p2))) → p2) ∨ p1) ∨ True)))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_85408221490785072394418587806 : ((((p3 → True) ∧ (((False ∨ p2) ∨ (p3 → True)) → (p5 ∧ False))) ∧ ((p5 ∨ (((p1 → p2) ∧ p2) ∨ p4)) ∨ ((p2 → p2) → p5))) → p2) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h8 : ((False ∨ p2) ∨ (p3 → True)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h9
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h10 := h5 h8
      -- We need to get the right conjuct of h10 based on <expert-advice>.
      let h11 := h10.right
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h16 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h17 : ((False ∨ p2) ∨ (p3 → True)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h18
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h19 := h5 h17
        -- We need to get the right conjuct of h19 based on <expert-advice>.
        let h20 := h19.right
        -- False on the left can always be used.
        apply False.elim h20
  case inr h21 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h22 : ((False ∨ p2) ∨ (p3 → True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h23
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h24 := h5 h22
    -- We need to get the right conjuct of h24 based on <expert-advice>.
    let h25 := h24.right
    -- False on the left can always be used.
    apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227474977873862835376995572196 : ((True ∧ (p3 ∧ p1)) ∨ (((p3 ∧ (True ∨ p3)) ∨ ((p5 → p4) ∧ p4)) → ((p2 ∧ ((p4 → p2) → (p4 ∧ (p4 ∧ True)))) ∨ (False → p1)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135958178370121099531881904821 : (((True ∧ ((((False → p1) ∨ (p2 ∧ p1)) ∨ p1) → p3)) ∧ (p4 ∧ (True ∨ (((p1 → p3) ∨ (p5 ∧ p1)) → p4)))) ∨ (False ∨ (p5 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136096263189533731825423201778 : ((((p4 ∨ ((p1 ∨ (p2 ∧ p5)) ∨ False)) ∨ p3) ∨ ((p2 ∧ ((False → (p5 → p1)) → (True ∨ (p2 ∧ p3)))) → False)) ∨ (True → (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49875007150497797698753929011 : (((((False ∧ (False ∧ (((p5 ∨ (p1 → p3)) → (p1 ∨ ((True → p4) ∧ False))) ∧ p2))) ∧ p2) ∨ p1) ∧ ((p1 ∧ (p1 → False)) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_15078353512910912671549558624 : (((p3 ∧ (((p5 ∧ False) ∧ (((p2 → p2) ∧ ((((p2 ∧ (p3 ∨ False)) → True) ∧ p4) ∨ (p5 → p4))) → True)) ∧ False)) ∨ (p1 ∨ True)) ∧ True) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694084615780980226898317969488 : (((((False ∧ (p5 ∧ (((p4 ∨ p2) ∧ p4) ∨ p3))) ∨ ((False ∧ p4) → p3)) ∨ (True ∨ (((False ∨ p2) ∨ p4) ∧ ((p5 ∨ p5) → p5)))) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_783571506589098211104109622934 : (((p3 ∨ ((((p1 → p3) → (p2 → (p1 → (p3 ∧ False)))) → p1) ∨ ((((True → False) → (p5 ∧ p2)) ∧ (True ∨ p2)) → (p2 ∨ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197559805122026436078742019028 : ((((p3 → (p2 ∧ False)) → False) ∨ (p5 ∧ p3)) ∨ ((p5 ∧ p4) → (((p2 → (p3 ∧ ((p5 → p5) → p5))) ∨ p5) ∧ ((p5 ∨ p3) ∧ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351814673031916558755702965518 : (p4 → (((p3 ∧ ((p4 ∨ (p5 ∧ p1)) ∧ (p5 ∨ (p2 → p1)))) → p1) ∨ (p5 → (((((p3 ∧ p3) ∧ False) ∧ p5) ∨ p2) ∨ (p4 ∨ p5))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138025538854644942934854653414 : ((True → (((((p5 ∧ ((False → p3) ∨ ((True → True) → (p1 → (False ∨ p3))))) ∧ p2) ∨ False) ∨ p1) ∧ (p4 ∨ p5))) ∨ ((p5 ∨ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_757979255731941536745141782008 : (((p1 ∧ (True → ((((((p5 → False) → ((((p4 ∨ (p5 ∧ (p1 ∧ p2))) ∨ False) ∧ p3) → True)) ∨ p5) ∧ (p1 ∧ p1)) ∨ p3) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738192952695255883767024847652 : ((((False ∧ p3) ∨ ((((p5 → (((((p5 → (True → p4)) → p2) ∧ p4) ∨ p3) ∨ p5)) ∨ False) → ((p3 → (p1 → False)) ∧ p1)) → p1)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p5 → (((((p5 → (True → p4)) → p2) ∧ p4) ∨ p3) ∨ p5)) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316474076540822392163163142230 : (p3 ∨ (p1 ∨ (p5 ∨ (((((((p5 → p4) ∧ p2) ∨ p4) ∧ (True ∨ p4)) ∧ (p1 ∧ (p4 → True))) ∧ p5) ∨ (((p4 → p3) ∧ p5) → True))))) := by
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
theorem thm_5_vars_122453763764530470446487188239 : ((((True ∨ (p3 → (((p3 → p3) ∧ p4) → p5))) ∨ ((False ∧ ((True ∧ False) ∨ (p1 ∨ p4))) → (p5 ∨ p1))) ∨ (p2 ∨ p5)) → (p4 ∨ True)) := by
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
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h5 =>
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
theorem thm_5_vars_114389912392311203358048799398 : (((((p2 → p1) ∧ ((p1 ∧ (p2 → ((p1 → (False ∨ p2)) ∨ p5))) ∨ p4)) → (p1 ∨ False)) ∨ (False ∨ ((True ∨ p2) → False))) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232068585584819861847393708003 : (((p4 ∨ p1) → False) → (p1 → (((p1 ∨ ((p4 ∧ ((((p2 ∧ p3) ∨ p3) → p2) → (p4 ∨ p1))) ∧ False)) → (False ∨ (False ∧ False))) ∧ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h5 : (p4 ∨ p1) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h6 := h1 h5
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- False on the left can always be used.
    apply False.elim h9
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h12 : (p4 ∨ p1) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h13 := h1 h12
  -- False on the left can always be used.
  apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_660787511587294695801862506758 : ((((((False ∧ p1) ∨ ((((((p1 ∨ (False ∧ True)) ∨ p5) ∧ (p5 ∧ (True → (p5 ∧ p1)))) ∧ p4) → p5) → p4)) → p1) → (p3 ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114396518482214354706628383619 : ((((False ∧ ((False ∧ ((p5 → p3) ∧ True)) ∧ (p1 ∧ p4))) ∧ ((True ∧ (p4 ∧ False)) → p5)) ∨ (p4 ∨ (p5 → (False ∧ p4)))) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606776737800648168714197375698 : ((((((((p2 → (((p5 → p2) ∨ p2) ∨ ((True ∨ (p1 ∧ p5)) ∨ p5))) ∨ False) ∨ (p1 ∧ (p1 ∧ p1))) → (False ∧ False)) ∧ False) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328398590202007679001203157116 : (True → ((p3 → ((p5 ∨ p4) ∨ ((True → (((p2 ∧ p4) ∨ p1) ∧ p5)) ∨ (True → (True ∨ False))))) ∧ (True ∨ (((p3 → p5) → True) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358723923963817221341606932178 : (p5 → (p5 → ((p5 ∨ (True → (p5 → ((p2 ∧ (((p2 → p4) ∧ True) ∧ True)) ∨ False)))) → (((p4 → p3) ∨ (False ∨ True)) ∧ (p5 ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190333305458893787466656977562 : ((((True ∨ ((False ∧ p5) → p4)) → (False ∧ p3)) ∨ True) ∨ ((False ∧ (p3 ∧ True)) ∧ (((p5 ∧ (p3 ∨ True)) ∧ (p3 → (p1 ∨ p3))) ∧ True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61205157932479984493349009752 : ((False ∧ ((True ∨ p4) → (((False ∧ p2) ∨ (p5 ∨ (((p3 ∧ ((((p4 ∨ (p3 ∧ p4)) → p5) ∨ True) ∧ False)) ∧ p4) ∨ p5))) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50300676597562331402280997290 : ((((((p3 ∧ p5) ∨ ((False ∨ (True ∨ (p3 ∨ p3))) ∧ (False → False))) ∨ True) → (p4 → (p5 ∨ p3))) ∨ ((True ∨ (p1 → False)) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186786691621212605080963815465 : (((((False → p4) ∨ p5) ∨ p5) ∧ (((p1 ∨ False) → p1) ∧ True)) → ((((p2 → p5) → False) ∨ ((p1 ∧ p3) ∧ p2)) ∨ (True ∨ (False ∨ True)))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h3.left
      let h10 := h3.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h3.left
    let h13 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40905443353824142802751043463 : ((((False ∧ (p2 ∧ ((((False ∨ ((p4 → p2) → p2)) ∧ ((p1 → (False → p5)) → (False → False))) ∨ p5) ∧ p5))) ∧ (False ∧ p4)) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611736705190032605409198164836 : (((((True → (((p2 ∧ True) → p2) ∧ ((True ∧ (((((p2 ∨ p2) ∨ p5) ∧ p5) ∧ p4) → (p4 ∨ p1))) ∧ (p3 → p3)))) → p3) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_134282296739261159692820515058 : ((((p2 ∧ p4) ∨ (p3 ∨ ((p3 → p2) → (p4 ∨ ((p3 ∨ True) ∨ (p5 ∨ ((p1 ∧ (False ∧ p3)) → p5))))))) ∨ False) ∨ ((False ∧ True) ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_37888942540866071616969850563 : ((((((False ∧ (((p4 ∧ (p4 ∧ (((True → (False → True)) → False) ∧ False))) → (True ∨ p1)) ∨ True)) → p5) → False) ∧ (p1 ∨ p1)) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324355954479667002004866700271 : (p5 ∨ (((((p4 → p5) ∧ p3) ∧ p3) ∨ p1) ∨ ((((p3 ∧ (p1 ∧ ((p2 ∨ p3) → (p3 → p2)))) ∨ p1) ∧ p4) → (False → (p3 ∧ p2))))) := by
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
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191144739844704017683315127150 : ((((p3 ∨ False) ∨ p5) ∨ (((p1 ∧ True) ∧ False) ∧ p3)) ∨ ((((p5 ∧ (p5 → p1)) ∨ p4) → (p2 → True)) ∨ (p3 → ((p1 ∨ p3) ∧ p5)))) := by
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
theorem thm_5_vars_117649495302839819741158583966 : ((p3 ∧ (((((p3 → p2) ∧ False) → (p5 ∨ ((p1 → (p4 → ((p3 ∧ True) → p2))) ∨ (p2 ∧ p4)))) → False) ∧ (p5 → True))) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136405561906719461866747261409 : (((p1 → (p4 ∧ (False → p1))) ∨ ((((p3 → False) → p2) ∨ True) → (p1 ∨ (p5 → (False ∧ (True ∧ (p5 → p2))))))) ∨ (True ∧ (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254362269004954907252647849820 : ((p2 ∧ p4) → ((p3 ∨ (True ∨ True)) → ((((p3 ∨ p4) → (True ∧ (p1 → ((p1 ∨ p3) → p1)))) → ((True ∨ p3) ∧ (True → False))) → False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h1.left
    let h6 := h1.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h7 : ((p3 ∨ p4) → (True ∧ (p1 → ((p1 ∨ p3) → p1)))) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h9
      -- Implications on the right can always be decomposed.
      intro h10
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h12 =>
          -- One of the premise coincides with the conclusion.
          exact h9
        case inr h13 =>
          -- One of the premise coincides with the conclusion.
          exact h9
      case inr h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h15 =>
          -- One of the premise coincides with the conclusion.
          exact h9
        case inr h16 =>
          -- One of the premise coincides with the conclusion.
          exact h9
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h17 := h3 h7
    -- We need to get the right conjuct of h17 based on <expert-advice>.
    let h18 := h17.right
    -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
    have h19 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h18, we can now drive its conclusion.
    let h20 := h18 h19
    -- False on the left can always be used.
    apply False.elim h20
  case inr h21 =>
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h1.left
      let h24 := h1.right
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h25 : ((p3 ∨ p4) → (True ∧ (p1 → ((p1 ∨ p3) → p1)))) := by
        -- Implications on the right can always be decomposed.
        intro h26
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Implications on the right can always be decomposed.
        intro h27
        -- Implications on the right can always be decomposed.
        intro h28
        -- Disjunctions on the left can always be decomposed.
        cases h28
        case inl h29 =>
          -- Disjunctions on the left can always be decomposed.
          cases h26
          case inl h30 =>
            -- One of the premise coincides with the conclusion.
            exact h27
          case inr h31 =>
            -- One of the premise coincides with the conclusion.
            exact h27
        case inr h32 =>
          -- Disjunctions on the left can always be decomposed.
          cases h26
          case inl h33 =>
            -- One of the premise coincides with the conclusion.
            exact h27
          case inr h34 =>
            -- One of the premise coincides with the conclusion.
            exact h27
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h35 := h3 h25
      -- We need to get the right conjuct of h35 based on <expert-advice>.
      let h36 := h35.right
      -- We want to use the implication h36 based on <expert-advice>. So we show its premise.
      have h37 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h36, we can now drive its conclusion.
      let h38 := h36 h37
      -- False on the left can always be used.
      apply False.elim h38
    case inr h39 =>
      -- Conjunctions on the left can always be decomposed.
      let h40 := h1.left
      let h41 := h1.right
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h42 : ((p3 ∨ p4) → (True ∧ (p1 → ((p1 ∨ p3) → p1)))) := by
        -- Implications on the right can always be decomposed.
        intro h43
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Implications on the right can always be decomposed.
        intro h44
        -- Implications on the right can always be decomposed.
        intro h45
        -- Disjunctions on the left can always be decomposed.
        cases h45
        case inl h46 =>
          -- Disjunctions on the left can always be decomposed.
          cases h43
          case inl h47 =>
            -- One of the premise coincides with the conclusion.
            exact h44
          case inr h48 =>
            -- One of the premise coincides with the conclusion.
            exact h44
        case inr h49 =>
          -- Disjunctions on the left can always be decomposed.
          cases h43
          case inl h50 =>
            -- One of the premise coincides with the conclusion.
            exact h44
          case inr h51 =>
            -- One of the premise coincides with the conclusion.
            exact h44
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h52 := h3 h42
      -- We need to get the right conjuct of h52 based on <expert-advice>.
      let h53 := h52.right
      -- We want to use the implication h53 based on <expert-advice>. So we show its premise.
      have h54 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h53, we can now drive its conclusion.
      let h55 := h53 h54
      -- False on the left can always be used.
      apply False.elim h55



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_487699364726659555202976550804 : ((((((False ∧ False) → p5) ∧ (p5 → False)) → ((True ∨ p1) ∧ (True ∧ ((((((p2 → p4) ∨ True) ∨ (p3 → p3)) ∧ p4) ∨ True) ∧ True)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46402557878224712629441977707 : ((((p3 → (((p2 ∧ (p3 ∧ p1)) ∨ p5) ∨ p3)) ∧ ((False ∨ False) ∧ (p1 ∨ (((True ∨ p3) ∧ p5) ∧ (p2 ∧ p4))))) ∧ (p2 ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200674769639607907876776902914 : ((p1 ∧ (p2 ∨ ((p2 → (p3 → p3)) ∨ p5))) → ((p4 ∨ True) ∧ (((p1 → (False → p1)) → False) ∨ (((p2 → True) ∧ False) ∨ (False → p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h16
      -- False on the left can always be used.
      apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185482245819653669755659137395 : ((p1 ∨ (p5 ∨ ((p3 → True) → (True → ((True ∧ p4) ∧ True))))) ∨ (False ∨ (((p4 → ((p3 → (p2 → p4)) ∨ (p1 ∧ p2))) ∨ False) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1



