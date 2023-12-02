variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166821955285144086998088239598 : (((((p4 → ((((p2 → p3) → ((p3 ∧ True) ∧ p5)) → True) ∧ p1)) ∨ False) ∨ True) ∧ p3) → (((False ∨ (p1 → p3)) ∧ (False ∨ p5)) → p5)) := by
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
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h1.left
      let h10 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- One of the premise coincides with the conclusion.
          exact h8
        case inr h13 =>
          -- False on the left can always be used.
          apply False.elim h13
      case inr h14 =>
        -- One of the premise coincides with the conclusion.
        exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_716405590387313594425212001671 : (((((False → p3) ∧ (p4 ∨ p1)) ∧ ((False ∧ False) ∧ ((p4 ∧ (((p5 ∧ (p5 ∧ (p3 ∧ False))) → p4) ∨ (p3 ∧ (p4 ∧ True)))) ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809964017668394639722167410880 : (((p5 → ((((p2 ∧ (p4 → p2)) ∧ p3) ∧ ((((p2 → p3) ∨ p4) ∧ (p3 ∨ p1)) → (False ∨ (p4 ∧ p3)))) ∨ ((p1 → p3) ∨ True))) ∨ p5) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165201171078377089196278332724 : ((((False ∨ ((False → p4) ∧ ((p3 ∧ (p3 → p5)) ∧ (p1 → p4)))) ∨ False) ∨ (p3 ∧ False)) ∨ (((True ∧ False) → (True → (p5 ∧ p2))) ∨ p2)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37598625263200567525511892515 : (((((((p4 ∨ p5) ∨ ((False ∨ ((p3 ∧ (p1 → False)) ∨ (p2 ∨ (p5 ∨ (p2 ∧ p5))))) ∧ (p1 → True))) ∧ True) ∧ p3) → p4) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58576207162472647176026034208 : (((True → p3) ∧ ((p3 → ((p1 ∧ p1) → (False → (((False ∧ p2) → p1) ∧ ((p4 ∧ p2) ∧ p4))))) → (((p5 ∧ p3) ∨ p5) ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_686878452491956504003454178018 : ((((True ∨ (((p5 ∨ p4) → p4) ∧ (p3 ∨ (((p1 ∧ p5) → (False → True)) → (True ∨ p3))))) → (True → ((True → (p1 ∧ p1)) ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179633763383204047259603032803 : ((p4 → ((p5 ∨ p4) → ((((p1 → p3) → False) ∨ p5) ∨ (p2 → p2)))) ∨ (((((False → p4) ∨ (p5 ∨ True)) → p1) ∧ (p4 → p3)) → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148661679578464672105793317311 : (((False ∨ (p5 → (((p3 → p1) ∨ p1) → p3))) ∧ (p2 ∨ (False ∨ ((((True ∨ p4) → True) ∧ p4) → True)))) ∨ (p5 ∨ ((True ∨ False) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_86674858412104008881169123683 : ((((p1 → p5) → (((p4 ∨ p2) ∨ p4) ∧ True)) ∧ ((False ∨ (p5 ∧ (((p3 ∨ p5) ∧ p3) → (p1 ∨ p5)))) ∧ ((p2 → p2) ∨ p4))) → p5) := by
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
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h10 =>
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h11 =>
      -- One of the premise coincides with the conclusion.
      exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147302494993839997671485619710 : ((((((p4 ∧ (p2 ∨ (((p3 ∧ True) ∧ (True → p2)) ∧ True))) ∨ p3) ∨ ((p4 ∨ p4) ∧ True)) → False) ∨ p1) ∨ (True ∨ ((p2 ∧ p3) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184800288497449294301504121066 : (((p5 ∧ ((p2 ∧ p1) ∧ p4)) ∨ ((p1 ∨ (p2 ∧ p1)) ∧ p3)) ∨ (((p2 → ((p4 ∨ (p2 → (False ∨ (p1 ∨ p2)))) ∧ True)) ∨ p1) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51200669599049015986295326419 : (((((True ∨ ((False ∧ (p3 → p2)) → False)) → (p2 ∧ p5)) ∨ (((p3 ∨ p1) ∧ True) ∨ p1)) ∨ ((p1 ∧ (p3 ∨ p4)) ∨ (p3 ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151627073041189946137908909529 : (((False → ((p2 ∨ (False ∧ True)) ∨ (((p2 ∨ True) ∨ ((p1 → p5) ∧ (p3 → False))) ∧ p1))) → (p2 ∨ p5)) → (p5 ∨ ((p3 ∧ p1) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → ((p2 ∨ (False ∧ True)) ∨ (((p2 ∨ True) ∨ ((p1 → p5) ∧ (p3 → False))) ∧ p1))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185063888523206265471986191647 : (((p2 ∧ p4) ∨ (((True ∧ False) ∨ (p4 ∨ False)) ∨ (p4 ∨ p5))) ∨ (((True ∨ p2) ∧ (((True ∧ ((False ∧ p2) ∧ p5)) ∧ p5) ∨ True)) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_206776709079682370126470113371 : ((p4 → ((p3 → p1) ∧ (False ∨ True))) ∨ (((False ∧ (True → (p4 ∨ ((p2 ∨ ((True ∧ p3) ∨ p5)) ∧ p3)))) ∨ ((p3 ∧ True) ∨ True)) ∨ p5)) := by
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
theorem thm_5_vars_116671735857309512802734152299 : (((p5 → False) ∧ (((((True → p3) ∨ p4) ∨ ((p5 → p1) ∨ p5)) → False) ∨ (((False → (p4 → (False ∧ True))) ∨ True) ∧ p1))) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152203216937516807675234745381 : (((((p2 ∨ p4) → (p1 ∧ False)) ∧ p5) ∧ ((p4 ∨ p1) ∨ (p1 ∧ (((p3 → (p5 ∧ p4)) ∨ p2) → p2)))) → ((p4 ∨ p2) → (p4 ∧ p5))) := by
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
    let h4 := h1.left
    let h5 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h10 =>
        -- One of the premise coincides with the conclusion.
        exact h3
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h1.left
    let h16 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h17 := h15.left
    let h18 := h15.right
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h19 =>
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h20 =>
        -- One of the premise coincides with the conclusion.
        exact h20
      case inr h21 =>
        -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
        have h22 : (p2 ∨ p4) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h14
        -- We have shown the premise of h17, we can now drive its conclusion.
        let h23 := h17 h22
        -- We need to get the right conjuct of h23 based on <expert-advice>.
        let h24 := h23.right
        -- False on the left can always be used.
        apply False.elim h24
    case inr h25 =>
      -- Conjunctions on the left can always be decomposed.
      let h26 := h25.left
      let h27 := h25.right
      -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
      have h28 : (p2 ∨ p4) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h14
      -- We have shown the premise of h17, we can now drive its conclusion.
      let h29 := h17 h28
      -- We need to get the right conjuct of h29 based on <expert-advice>.
      let h30 := h29.right
      -- False on the left can always be used.
      apply False.elim h30
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h31 =>
    -- Conjunctions on the left can always be decomposed.
    let h32 := h1.left
    let h33 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h34 := h32.left
    let h35 := h32.right
    -- Disjunctions on the left can always be decomposed.
    cases h33
    case inl h36 =>
      -- Disjunctions on the left can always be decomposed.
      cases h36
      case inl h37 =>
        -- One of the premise coincides with the conclusion.
        exact h35
      case inr h38 =>
        -- One of the premise coincides with the conclusion.
        exact h35
    case inr h39 =>
      -- Conjunctions on the left can always be decomposed.
      let h40 := h39.left
      let h41 := h39.right
      -- One of the premise coincides with the conclusion.
      exact h35
  case inr h42 =>
    -- Conjunctions on the left can always be decomposed.
    let h43 := h1.left
    let h44 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h45 := h43.left
    let h46 := h43.right
    -- Disjunctions on the left can always be decomposed.
    cases h44
    case inl h47 =>
      -- Disjunctions on the left can always be decomposed.
      cases h47
      case inl h48 =>
        -- One of the premise coincides with the conclusion.
        exact h46
      case inr h49 =>
        -- One of the premise coincides with the conclusion.
        exact h46
    case inr h50 =>
      -- Conjunctions on the left can always be decomposed.
      let h51 := h50.left
      let h52 := h50.right
      -- One of the premise coincides with the conclusion.
      exact h46



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_664748172599333500188992600924 : ((((False → (p5 → (((p4 → p2) ∧ p4) ∧ ((p2 ∨ (((p5 → (True → (p3 ∨ p2))) ∧ (p2 → p1)) ∨ p4)) ∨ p3)))) → (p1 ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694734079939304242969361245295 : ((((p3 ∨ (True ∧ (p5 → (False ∧ ((p5 → (p4 ∨ p3)) → (True ∨ True)))))) ∨ (((p2 ∨ (p1 ∧ p3)) → (p1 ∧ (p2 ∨ False))) ∨ True)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_126106480443319822457954218860 : ((True ∧ ((True → (((False ∨ ((p3 → p5) → False)) ∨ (p4 ∧ p3)) ∧ ((p1 ∧ (p4 ∨ (False ∨ p4))) ∧ False))) ∧ (False → p1))) → (p1 ∧ p2)) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- One of the premise coincides with the conclusion.
  exact h10
  -- Conjunctions on the left can always be decomposed.
  let h11 := h1.left
  let h12 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h13 := h12.left
  let h14 := h12.right
  -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
  have h15 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h13, we can now drive its conclusion.
  let h16 := h13 h15
  -- We need to get the right conjuct of h16 based on <expert-advice>.
  let h17 := h16.right
  -- We need to get the right conjuct of h17 based on <expert-advice>.
  let h18 := h17.right
  -- False on the left can always be used.
  apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184468257153135007631999228921 : ((((((p2 ∧ False) → p4) → (p3 ∨ p3)) ∧ p1) ∨ (p2 → True)) ∨ (p4 ∨ ((False ∧ ((p1 ∧ p5) ∨ p4)) ∧ (True ∨ ((p2 → p1) ∨ True))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63389766275468504584135776752 : ((p5 ∧ (p1 ∨ ((p2 ∨ (((((True ∧ p2) ∧ True) ∧ p4) → (p5 ∧ True)) → ((True ∨ (p4 ∨ (p2 ∧ (p5 ∨ p2)))) → False))) → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789531747124233266832335015331 : (((p5 ∨ ((False ∧ (((p2 ∧ (True → p5)) ∨ (p2 ∨ p5)) ∧ p1)) ∨ ((p5 ∧ ((p3 ∧ p3) ∨ (True ∨ (p5 → p1)))) ∧ (False ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138043498196584246100980475092 : ((True → ((((False ∧ True) ∧ True) ∨ False) ∧ ((p1 ∨ p4) → (((p4 ∧ (p3 → False)) ∧ ((True ∨ p4) ∧ p3)) ∨ p2)))) ∨ (False → (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115004489536759358942326588325 : ((((True ∧ (p5 ∧ False)) ∧ (((False → p5) → p4) ∧ (p4 ∧ p2))) ∧ (((p2 ∧ p1) ∧ (p5 ∨ p4)) ∨ (False ∨ (p5 ∨ False)))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_155228299859342046490836183662 : (((p5 ∨ ((p2 ∨ (p2 ∨ p2)) ∧ (p4 ∧ p3))) ∨ (p4 ∨ ((False → False) → (True ∨ (p3 ∨ p3))))) ∧ ((p2 ∨ (p3 → p4)) ∨ (p4 → True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53088792448239390312719465069 : (((p1 ∨ ((p5 ∨ (((False → False) ∧ False) ∧ (p5 ∧ p4))) ∨ True)) ∧ ((((((p1 → p5) → p2) → (p3 → p2)) ∧ p1) ∧ p5) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317945976251282198465972168815 : (p4 ∨ ((p3 ∨ ((p5 ∧ False) ∨ (p4 ∨ (((p3 ∨ p5) → (p3 → ((p1 ∨ (p1 → (p5 ∨ p3))) ∧ p2))) ∧ ((True → p2) → p3))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111942205437402803869568533175 : (((((p5 → (p1 ∧ (True → p2))) → (False ∨ (True ∨ p4))) → ((((p1 ∧ True) ∨ p1) → (p2 ∧ (p1 ∧ True))) ∧ p3)) ∨ p4) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678816699919314179531212867368 : ((((False ∧ ((p2 → ((True → (((p2 ∨ (True ∧ p5)) → p5) ∧ p1)) ∧ (p5 ∨ (False ∧ p1)))) ∨ p2)) ∨ ((False ∨ (True ∨ False)) ∨ p1)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_104709335033718215613478085070 : (((p5 → (((p5 ∨ (p3 ∨ p2)) ∧ ((p5 ∧ (p1 ∨ (True → (p2 ∧ p3)))) ∧ p3)) ∧ ((False ∧ p3) ∨ True))) ∨ (p3 → p3)) ∧ (True → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4068964528020508778396007705 : (p2 ∨ (p2 ∨ (((p4 → p4) ∨ p1) → ((p1 ∨ ((p1 ∨ (p4 ∧ p2)) ∨ ((False ∨ ((p4 ∨ True) ∨ False)) ∨ True))) ∨ (True ∧ p4))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41705431239509642181859147381 : (((((p1 ∨ False) → ((p4 → p5) ∧ p4)) → ((p5 ∨ (p4 ∨ (p1 ∨ (p4 → p4)))) ∨ ((p5 ∨ (p2 ∧ (p5 ∧ p4))) → p5))) ∨ p4) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60139364528187756756720383174 : (((p4 ∨ p1) → ((False ∨ (p1 → (((True ∨ False) ∧ (p5 ∨ False)) ∧ ((p5 → p5) ∧ (True ∧ p5))))) ∨ ((p1 ∨ (p4 ∨ p1)) → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731699160360786111588156670601 : ((((p2 → (p3 ∨ p3)) → (p3 ∧ (False ∧ ((False ∨ (((p5 → (p1 → (p2 ∧ p4))) ∧ p2) ∨ (True ∨ ((p2 → True) ∧ p5)))) ∨ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57645347758864439118296217989 : ((((False ∨ p1) ∨ p5) → ((((p2 ∧ (p3 → (p3 ∨ p5))) → True) ∧ ((p5 ∧ p4) ∨ ((p4 → False) → ((True → True) → p2)))) ∨ True)) ∨ p4) := by
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
      -- False on the left can always be used.
      apply False.elim h3
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
theorem thm_5_vars_767287928844908657525891713952 : (((p5 ∧ ((((p3 ∧ False) ∨ ((False ∧ p3) ∨ ((((p3 ∨ p3) ∧ (p4 ∧ p4)) ∧ True) ∨ (True → True)))) → ((p3 ∨ False) ∧ True)) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50481938994041391467966164994 : (((p2 → (p5 ∨ ((p3 ∧ ((p3 → (False → (p5 → True))) ∨ ((False ∧ p1) ∨ True))) ∨ (p4 ∧ True)))) ∨ ((p2 ∧ (p4 ∨ p3)) → True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44128074073019937326662502880 : (((((p3 ∧ p1) ∨ ((((p2 ∨ p1) ∨ ((p5 ∨ ((p5 ∧ p3) ∨ True)) ∧ p4)) ∨ p1) → (p3 → p1))) ∨ ((False → p3) ∧ p4)) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68924036032796603905657757801 : ((p4 → (p2 ∨ ((p5 → True) ∧ (p3 ∧ ((((p2 ∨ (((p1 → (p3 ∨ (p4 → p1))) ∨ False) → p1)) ∨ p2) → (p3 ∧ p2)) ∨ True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46432016357205018390279951321 : (((((((p2 → p4) → p1) ∧ False) ∨ p4) → (p4 → (((p3 ∨ p5) ∨ (p4 → ((False → False) → p1))) ∨ (p3 → True)))) ∧ (True ∨ p1)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314282828793706995539622172082 : (p3 ∨ ((p1 → (((p5 ∨ p5) ∧ ((p3 ∧ (p4 ∨ False)) ∧ (((True ∧ False) → p1) ∨ (True → False)))) ∨ (p1 ∨ p4))) ∨ ((p1 ∧ True) ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_156976498147162499550393995124 : (((((p2 ∨ p3) ∧ ((p1 → True) ∧ (p4 ∧ p3))) ∧ (p1 ∧ (p1 ∧ ((p1 ∧ p2) ∨ False)))) ∨ p4) ∨ ((p2 → (False ∨ p3)) ∨ (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60713588873224780687441628920 : ((True ∧ ((p1 ∧ (p2 → (True ∧ (p2 ∧ p1)))) ∧ ((p2 ∨ (((p4 → p3) → (p1 ∧ False)) → (p1 ∨ (False ∧ (p5 → p2))))) ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112229776184392796916934379273 : (((p2 ∨ ((p5 ∨ ((((p2 ∨ (p2 ∨ p5)) ∧ p3) → ((p3 ∧ ((p4 ∨ p4) ∨ (p5 → p5))) ∧ p4)) → p1)) ∨ p1)) ∨ True) ∨ (p1 ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257987595445706462018852991122 : ((p4 ∨ p1) → (((((p4 ∨ False) ∧ ((((p4 ∨ p2) → True) → False) → ((p2 ∧ p2) ∨ p3))) ∨ (p4 → p5)) ∧ (p1 ∨ True)) → (p2 ∨ True))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
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
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h15 =>
      -- False on the left can always be used.
      apply False.elim h15
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h21 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h22 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156737125734352326064794048541 : ((((p1 ∧ (p5 → (p4 ∨ False))) ∨ (p1 → (True ∧ ((p5 ∨ (False ∨ True)) ∨ (p3 ∧ p1))))) ∧ p4) ∨ ((p1 ∧ (p1 ∧ (p1 → p4))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265929255851835699269389791371 : (True ∧ (True → (p4 → ((True ∨ p1) → ((((p5 ∧ (False → (p5 ∧ (p3 ∧ p2)))) → p1) ∨ False) ∨ ((p4 ∨ p1) ∧ ((True ∧ p4) → p4))))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705444740264287931146357878858 : (((((True → (p3 ∧ ((False ∧ False) ∨ p2))) ∨ p4) ∧ ((False ∨ p1) → (p4 → (((p2 ∨ p2) ∧ p4) ∧ (True → (True ∨ (p1 ∧ p5))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656968809882522847381048884395 : ((((((p3 ∨ (p1 → p1)) → True) → ((p1 → (((True ∨ (True ∧ p5)) → p4) → (p2 ∧ (p1 ∧ p1)))) ∨ (True → p5))) ∨ (p1 → p1)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_262147635647591029743684999778 : (True ∧ ((((((False ∨ ((p3 ∧ True) → (True ∧ p2))) ∨ False) ∨ (((p5 ∧ p2) ∧ ((p4 ∧ p5) ∧ p1)) ∧ p5)) ∧ (p3 ∧ p2)) ∨ p1) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_791468905959187289545798484769 : (((True → ((p1 ∧ (p5 → (p5 → (p1 → ((((p5 ∧ (p3 ∨ p2)) → p2) ∧ False) ∧ (p2 → ((p3 ∧ (False → p1)) ∧ False))))))) ∨ True)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_186131124421518808533590601088 : (((((p2 ∨ p5) ∧ p3) ∧ ((p5 ∧ p1) ∧ (False ∨ True))) ∨ p1) → ((p4 → p1) → ((False ∨ p2) ∨ (p3 ∨ (((p1 ∧ False) ∧ True) → p5))))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h5.left
      let h10 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h9.left
      let h12 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h13 =>
        -- False on the left can always be used.
        apply False.elim h13
      case inr h14 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h5.left
      let h17 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h18 := h16.left
      let h19 := h16.right
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h20 =>
        -- False on the left can always be used.
        apply False.elim h20
      case inr h21 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h7
  case inr h22 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h23
    -- Conjunctions on the left can always be decomposed.
    let h24 := h23.left
    let h25 := h23.right
    -- Conjunctions on the left can always be decomposed.
    let h26 := h24.left
    let h27 := h24.right
    -- False on the left can always be used.
    apply False.elim h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147521261362698658568355877308 : (((p5 ∨ (((((True → (False → p1)) ∨ (p5 ∨ False)) ∧ p1) → p3) ∧ ((p2 ∨ (p1 ∨ p4)) → True))) ∨ True) ∨ ((True ∨ p3) ∧ (False ∨ p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259378482051300851247999456034 : ((False → p3) → (((False ∨ (p2 ∨ (True ∨ p5))) → (((((p2 ∧ False) ∧ ((((p3 ∨ p1) ∨ False) → p1) ∨ p3)) → False) → False) ∧ True)) → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (False ∨ (p2 ∨ (True ∨ p5))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : (((p2 ∧ False) ∧ ((((p3 ∨ p1) ∨ False) → p1) ∨ p3)) → False) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- False on the left can always be used.
    apply False.elim h11
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h12 := h5 h6
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114304182288767723178651730568 : (((((p2 → p3) ∧ (False ∨ ((False → p4) → (False ∨ p1)))) ∨ (p2 ∧ ((False ∧ p1) ∨ True))) ∧ ((p2 → (p3 ∧ p4)) ∧ p4)) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246579826296300892105803299163 : ((p5 ∧ p2) ∨ ((p5 ∨ (((p1 ∨ p2) ∨ (p5 → p2)) → (False ∨ (p1 ∨ True)))) ∨ (((True ∧ (True → p3)) → (p3 ∧ p4)) ∧ (p2 ∧ p4)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h4 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_726554160201191890178087863309 : (((((p5 → p3) ∨ False) ∨ (((((p2 → p4) ∧ p2) → (True ∧ True)) → p2) ∧ (p4 → (((p5 ∨ True) → ((p3 ∧ p1) → p2)) → p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173992085209285776873992313318 : ((((p2 ∨ p5) ∨ (p5 ∨ ((False ∧ (True → False)) ∧ (p3 ∧ (p1 ∨ True))))) → p4) → (((p3 → True) → p3) ∨ (True → (p5 ∨ (True ∨ p3))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312227872762139979287588611282 : (p2 ∨ (p1 → (((((True ∧ p4) ∧ ((((p3 ∨ p4) → p3) ∧ (p2 ∨ True)) ∧ (p3 ∨ p3))) ∨ (((p1 ∧ True) → True) ∨ p4)) ∨ p3) ∨ False))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186366160309739204626055206736 : ((((p5 ∧ True) ∨ ((((p4 ∨ True) → p5) ∧ True) → p5)) → p4) → ((((p5 ∨ (((False ∨ (p2 ∧ p2)) ∨ False) → p2)) → p2) ∧ p3) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p5 ∧ True) ∨ ((((p4 ∨ True) → p5) ∧ True) → p5)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h6 : (p4 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h7 := h4 h6
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147180575836803500025909414279 : (((p2 ∨ ((((p1 → p3) ∨ p5) → ((((p5 ∧ p3) ∧ p3) ∨ (p3 → p5)) ∧ p2)) → (False ∨ p1))) ∧ p5) ∨ (True ∧ ((False → True) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215120465360026331283852660692 : (((p3 → False) → (p2 → False)) ∨ ((False ∧ ((False → (False → p1)) ∧ ((((p2 ∧ p5) ∨ p3) ∧ False) ∧ ((p2 → p5) → p2)))) ∨ (True ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174037387706154549978877235337 : (((p3 ∨ (False → ((p3 → ((False ∨ p1) ∨ (False ∨ True))) ∨ (False ∧ p4)))) → False) → (False ∧ (p2 ∨ ((((p4 → False) ∧ p2) ∨ p4) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 ∨ (False → ((p3 → ((False ∨ p1) ∨ (False ∨ True))) ∨ (False ∧ p4)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : (p3 ∨ (False → ((p3 → ((False ∨ p1) ∨ (False ∨ True))) ∨ (False ∧ p4)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h6
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h5
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51982552282441207622627014268 : ((((False ∧ p5) ∨ ((p2 ∨ ((p2 ∨ p3) → (p3 → p5))) ∨ (False → (p2 ∧ p4)))) ∨ ((((p4 ∧ p3) → False) ∨ (p1 → p2)) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345480955377083782252438434745 : (p3 → (((False → ((p2 → (p1 → ((p1 ∨ (False ∨ (p2 ∨ p4))) ∨ p4))) → ((p4 ∧ p1) → (True ∧ p1)))) → ((p4 ∨ False) ∧ p3)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689018255521491777680948595726 : (((((((p4 ∧ p5) ∧ (((p4 ∧ (p2 ∧ p1)) ∨ p3) ∨ p1)) ∨ (p4 ∨ True)) ∨ p2) ∨ ((p4 ∧ True) → ((p3 ∨ (p2 ∨ p2)) ∨ p2))) ∨ p3) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193683576762379172848382377411 : ((p1 ∧ ((p1 ∨ (((p4 → p4) → p3) ∨ p5)) → p2)) → (((((True ∨ p3) → p5) ∨ (p2 ∨ p5)) ∨ (((p5 ∨ p3) ∧ False) ∧ p3)) ∨ p1)) := by
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
theorem thm_5_vars_707338676403737469567489387500 : (((((p4 ∧ (p4 ∧ (True ∨ False))) ∨ (p3 ∧ p1)) ∨ ((((p4 → (p2 ∨ (p3 ∨ (True ∨ p2)))) → p1) ∨ p2) → ((True → False) → False))) ∨ p5) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h4
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h7
    -- False on the left can always be used.
    apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114761631769390523211371486496 : (((p5 ∨ ((((((p5 ∨ p2) ∧ (p2 ∨ p4)) ∧ p1) → p1) ∨ (p4 → p5)) ∨ p4)) → ((p2 ∧ ((False ∧ p5) ∧ p1)) ∨ True)) ∨ (p5 → p2)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149413022018376123380094202550 : ((True ∧ ((False ∨ ((p2 ∨ (p5 ∧ ((p4 ∧ p5) ∧ True))) ∧ p3)) ∧ (((False ∧ (p4 ∧ p4)) → True) ∧ p5))) ∨ ((p5 → p1) → (True ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356376661449215261122748315585 : (p5 → ((((((p5 ∨ (p4 ∧ p5)) ∨ p2) ∨ ((p2 ∧ p1) ∧ p3)) ∨ p3) → False) → ((((p3 → p4) ∧ p1) ∨ (p2 → (p4 ∧ p3))) ∧ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((((p5 ∨ (p4 ∧ p5)) ∨ p2) ∨ ((p2 ∧ p1) ∧ p3)) ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : ((((p5 ∨ (p4 ∧ p5)) ∨ p2) ∨ ((p2 ∧ p1) ∧ p3)) ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177794492439891007326355661222 : (((p1 ∨ ((p1 ∧ (((p2 ∨ p5) ∨ True) → p5)) ∨ (p3 ∧ p3))) ∧ p2) ∨ (False → ((True → ((p3 ∧ False) ∧ p3)) ∨ (p2 → (p5 → p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322817786381657445288111733114 : (p5 ∨ (((p1 ∧ ((p2 ∧ ((((p3 ∨ p1) ∧ p4) ∧ p4) ∧ (True → p5))) ∧ p2)) ∧ (((p3 ∨ p4) ∧ p2) ∧ (p4 ∨ (p3 → p2)))) → p5)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h9.left
  let h11 := h9.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h10.left
  let h13 := h10.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h12.left
  let h15 := h12.right
  -- Disjunctions on the left can always be decomposed.
  cases h14
  case inl h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h3.left
    let h18 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h19 := h17.left
    let h20 := h17.right
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h21 =>
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h22 =>
        -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
        have h23 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h11, we can now drive its conclusion.
        let h24 := h11 h23
        -- One of the premise coincides with the conclusion.
        exact h24
      case inr h25 =>
        -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
        have h26 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h11, we can now drive its conclusion.
        let h27 := h11 h26
        -- One of the premise coincides with the conclusion.
        exact h27
    case inr h28 =>
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h29 =>
        -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
        have h30 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h11, we can now drive its conclusion.
        let h31 := h11 h30
        -- One of the premise coincides with the conclusion.
        exact h31
      case inr h32 =>
        -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
        have h33 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h11, we can now drive its conclusion.
        let h34 := h11 h33
        -- One of the premise coincides with the conclusion.
        exact h34
  case inr h35 =>
    -- Conjunctions on the left can always be decomposed.
    let h36 := h3.left
    let h37 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h38 := h36.left
    let h39 := h36.right
    -- Disjunctions on the left can always be decomposed.
    cases h38
    case inl h40 =>
      -- Disjunctions on the left can always be decomposed.
      cases h37
      case inl h41 =>
        -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
        have h42 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h11, we can now drive its conclusion.
        let h43 := h11 h42
        -- One of the premise coincides with the conclusion.
        exact h43
      case inr h44 =>
        -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
        have h45 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h11, we can now drive its conclusion.
        let h46 := h11 h45
        -- One of the premise coincides with the conclusion.
        exact h46
    case inr h47 =>
      -- Disjunctions on the left can always be decomposed.
      cases h37
      case inl h48 =>
        -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
        have h49 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h11, we can now drive its conclusion.
        let h50 := h11 h49
        -- One of the premise coincides with the conclusion.
        exact h50
      case inr h51 =>
        -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
        have h52 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h11, we can now drive its conclusion.
        let h53 := h11 h52
        -- One of the premise coincides with the conclusion.
        exact h53



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_760436940173807089046904297030 : (((p2 ∧ (True ∧ (p1 → (True ∧ (((((p2 ∧ ((p3 ∧ p3) ∧ p1)) → p2) ∨ p2) ∧ (p4 → (p3 → ((False → p3) → p1)))) → p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115096332645468145695231098841 : (((p5 → (p3 ∨ ((((p4 ∧ (p2 → True)) ∨ p1) → p2) ∨ True))) ∨ (p4 → ((p4 ∨ (False → False)) ∧ ((False → p4) ∧ p2)))) ∨ (p3 → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693055531406087949452956375248 : ((((False ∧ (p5 ∧ (((False ∧ (False ∧ p5)) ∧ (p2 → p4)) → (p5 → True)))) ∧ ((((p4 → (p3 ∨ p5)) → (False → p3)) ∧ p4) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_586481553614772075040934397398 : ((((((p5 ∧ (True ∧ False)) ∨ ((((False ∨ p3) → (p5 ∧ True)) ∧ False) ∨ (p2 ∧ (p1 ∧ ((p4 ∨ p5) ∧ (True → p1)))))) ∧ p5) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185519371819232998300539955974 : ((p3 ∨ (((p2 ∧ (p2 ∨ (p2 ∨ (False ∧ False)))) ∨ p2) ∨ p4)) ∨ ((((False → ((p3 ∨ p5) → (p2 → p5))) ∨ (False ∨ p4)) ∨ False) ∧ True)) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h1
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259878145518314325120186782863 : ((p1 → p4) → ((((p1 → (True ∨ False)) → p5) ∨ (p1 → (p2 ∧ (True ∨ (p3 ∧ False))))) ∨ (False ∨ ((p3 ∧ p1) → (p1 ∧ (p4 → p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h2.left
  let h7 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56556126018823781828884649831 : (((p4 ∨ ((p5 ∨ p4) ∧ p4)) → (((True ∧ (p5 → ((p3 ∨ p5) ∨ (((p1 ∨ ((p2 ∨ p3) → False)) ∨ p1) ∧ p3)))) ∧ False) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209475689669918824824245751302 : ((p3 → ((False ∨ p1) ∧ (p2 ∨ p2))) → ((p4 → ((True ∧ False) ∧ (p4 ∨ (True ∧ ((p2 → True) ∧ ((p3 ∨ p3) → p5)))))) ∨ (True ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308565002601235915396408179835 : (p2 ∨ (((p4 ∨ ((p4 ∨ False) ∨ (p1 ∨ True))) ∨ ((((p3 ∧ True) → p2) ∧ p5) ∨ (((True ∧ (p3 → p1)) → p3) ∧ (p4 → p1)))) ∨ p5)) := by
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
theorem thm_5_vars_329346953849335328620329374120 : (True → (((p5 ∧ False) → p4) → ((p5 ∨ (((p3 → False) ∨ True) ∨ ((p5 ∨ p5) ∧ (False ∧ ((p1 ∨ p1) ∨ True))))) ∨ ((False → p1) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
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
theorem thm_5_vars_214152596885387158065606385925 : ((((False ∧ p1) → False) → p5) ∨ (True ∧ (((False ∨ (p1 ∨ (p5 → p1))) → (((((p1 → False) ∨ p1) ∧ p4) ∧ p5) ∨ (False → True))) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165633050433818195927187115495 : ((((False ∧ False) ∨ (p1 ∨ (p3 ∧ p5))) ∧ (((p5 → (False → True)) ∧ (p5 → p1)) ∨ False)) ∨ (True → ((p2 → p2) ∨ ((p1 ∨ p1) → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114733473026409132814679536653 : ((((p3 ∨ (False ∨ (p4 ∧ (True ∨ False)))) → (((True ∨ (p1 → p3)) ∨ p4) → True)) → (((p2 → (p5 → p3)) ∨ p5) ∨ True)) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_963709396901512652713007156779 : ((((p3 → p5) ∧ ((p3 ∨ (p4 ∧ (((p1 ∧ (p4 ∧ p3)) → p4) ∧ p3))) ∧ ((p4 → p1) → ((p4 → ((p5 ∧ p3) ∨ p3)) ∨ p3)))) → p5) ∧ True) := by
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
    have h7 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h7
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h14 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h13
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h15 := h2 h14
    -- One of the premise coincides with the conclusion.
    exact h15
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244392055416366060418325376441 : ((False ∧ p1) ∨ ((((p1 ∨ p2) → ((p4 → p5) ∧ p4)) ∨ ((p4 ∧ p3) ∧ (p5 ∨ True))) ∨ (p5 ∨ ((p1 ∧ p2) → ((False → p1) ∨ True))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261357848854054335417075841462 : ((p5 → False) → (False ∨ ((p5 ∨ (False ∧ (p3 ∨ (p1 → (p5 ∧ (((True ∨ (False ∨ p1)) → (p1 ∧ p5)) → p2)))))) ∨ ((p5 → p1) ∨ p4)))) := by
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199796454186268401407904341207 : ((((p4 → (p1 ∧ True)) ∧ p1) ∧ (p5 ∨ False)) → (True ∧ ((p4 ∧ (p3 ∧ True)) → (((p3 → ((p2 ∧ (False ∧ p2)) ∧ p1)) → False) ∧ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h12 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h13 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h14 := h3 h13
    -- We need to get the left conjuct of h14 based on <expert-advice>.
    let h15 := h14.left
    -- We need to get the right conjuct of h15 based on <expert-advice>.
    let h16 := h15.right
    -- We need to get the left conjuct of h16 based on <expert-advice>.
    let h17 := h16.left
    -- False on the left can always be used.
    apply False.elim h17
  case inr h18 =>
    -- False on the left can always be used.
    apply False.elim h18
  -- Conjunctions on the left can always be decomposed.
  let h19 := h2.left
  let h20 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h21 := h20.left
  let h22 := h20.right
  -- Conjunctions on the left can always be decomposed.
  let h23 := h1.left
  let h24 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h25 := h23.left
  let h26 := h23.right
  -- Disjunctions on the left can always be decomposed.
  cases h24
  case inl h27 =>
    -- One of the premise coincides with the conclusion.
    exact h27
  case inr h28 =>
    -- False on the left can always be used.
    apply False.elim h28



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41317685296886834156773237305 : ((((((p4 ∨ p1) → (p1 ∧ p1)) ∨ ((((p5 ∨ p1) → p4) ∧ p3) ∨ (p1 ∧ p1))) ∧ (p4 ∨ (False → ((p5 → True) ∧ False)))) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257736721064705720781819729614 : ((p3 ∨ p4) → ((((p4 ∧ (p2 ∨ (((p4 ∧ p2) → (False ∨ p1)) ∧ (True ∨ (p1 → False))))) ∨ ((True ∨ p1) ∨ (p3 ∨ p4))) → False) → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : ((p4 ∧ (p2 ∨ (((p4 ∧ p2) → (False ∨ p1)) ∧ (True ∨ (p1 → False))))) ∨ ((True ∨ p1) ∨ (p3 ∨ p4))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h4
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209485467294123692755677731379 : ((p3 → (False ∧ (False → (p5 → True)))) → ((p4 ∧ (p4 ∧ p1)) ∨ (((False → p3) → p3) → (p1 → (p2 ∨ ((p3 ∨ (p4 → True)) ∨ p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613713143347505329261092502165 : ((((((p2 ∨ (p5 → p3)) → (((True ∧ (p2 ∨ True)) ∧ (((False ∨ False) ∧ (p5 ∨ p4)) ∨ p5)) ∧ p2)) ∧ ((p1 ∧ p2) ∨ p1)) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_324916011169104640256620009123 : (p5 ∨ ((p4 ∧ p5) ∨ ((((p1 ∨ p1) ∨ p2) ∨ (p5 → (((((True → p5) → p2) ∧ (False ∧ p1)) ∧ p2) → (p2 ∨ p1)))) → (p4 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200694433473986311746128447688 : ((p2 ∧ ((True → (p3 → (p5 ∧ p2))) → p3)) → ((((p5 ∨ p1) → (p4 → (False ∧ p3))) ∧ p5) ∨ (((False ∧ p4) → (p2 ∧ p4)) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352744374165059740770747411967 : (p4 → ((True ∧ p5) → (((True → p3) ∧ (p5 ∧ ((p4 → ((p2 → False) → p1)) → False))) → ((True → p1) → (False ∧ ((p1 → p3) ∨ p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h2.left
  let h10 := h2.right
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h11 : (p4 → ((p2 → False) → p1)) := by
    -- Implications on the right can always be decomposed.
    intro h12
    -- Implications on the right can always be decomposed.
    intro h13
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h14 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h15 := h4 h14
    -- One of the premise coincides with the conclusion.
    exact h15
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h16 := h8 h11
  -- False on the left can always be used.
  apply False.elim h16
  -- Conjunctions on the left can always be decomposed.
  let h17 := h3.left
  let h18 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h19 := h18.left
  let h20 := h18.right
  -- Conjunctions on the left can always be decomposed.
  let h21 := h2.left
  let h22 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
  have h23 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h17, we can now drive its conclusion.
  let h24 := h17 h23
  -- One of the premise coincides with the conclusion.
  exact h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_673053203713334083325276186155 : (((((p2 → (((p2 ∧ ((p4 ∨ True) ∧ p2)) ∨ p4) ∨ (p4 → (p3 ∧ False)))) → ((p4 → p2) → (p4 → p2))) → ((p1 ∧ p3) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



