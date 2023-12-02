variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216076789596448547638085419303 : ((True → ((True ∧ p3) ∧ p2)) ∨ ((((p2 ∧ ((p3 ∨ (False ∨ (p4 ∧ p1))) → p3)) ∧ ((p2 ∨ (p3 → p5)) → (p3 ∨ p4))) → p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345480178012308786262890526261 : (p3 → (((p5 ∧ (((((p3 ∧ ((p1 ∨ (p5 ∧ p1)) ∧ (p4 → False))) → p3) ∧ p5) ∨ p5) ∧ (True → p1))) → ((p1 ∨ False) ∨ p2)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h10 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h11 := h6 h10
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h13 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h14 := h6 h13
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65775931360639492646674081537 : ((p4 ∨ (((((p5 ∨ (p2 → (p3 ∧ (p2 → (False ∨ True))))) ∨ p3) ∧ True) → True) ∧ ((p4 → (p1 ∧ (p1 → (p2 ∧ p2)))) ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41952855558714460780920277820 : ((((p2 ∧ p3) ∧ ((p1 ∧ p4) ∨ (p4 → (((((p5 ∨ (p4 ∨ (p1 ∧ (p2 ∨ p3)))) → p1) ∧ p3) → (True → True)) → p4)))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_803870974757653546695952981785 : (((p3 → (((((True → p4) → ((True ∧ p4) ∨ ((False → p2) ∨ (False → p5)))) ∧ ((p5 ∧ (p2 ∧ p1)) ∨ p4)) ∧ True) → (p3 → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_927259868070650944368885967663 : ((((((True ∨ (p4 → (p5 ∨ (p2 → True)))) ∨ p5) ∧ p4) ∧ (p2 ∨ (True → ((((p5 ∨ ((False ∧ p4) ∨ True)) ∨ p5) ∨ p1) ∧ False)))) → p2) ∧ True) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h8 =>
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h9 =>
        -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
        have h10 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h9, we can now drive its conclusion.
        let h11 := h9 h10
        -- We need to get the right conjuct of h11 based on <expert-advice>.
        let h12 := h11.right
        -- False on the left can always be used.
        apply False.elim h12
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h14 =>
        -- One of the premise coincides with the conclusion.
        exact h14
      case inr h15 =>
        -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
        have h16 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h15, we can now drive its conclusion.
        let h17 := h15 h16
        -- We need to get the right conjuct of h17 based on <expert-advice>.
        let h18 := h17.right
        -- False on the left can always be used.
        apply False.elim h18
  case inr h19 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h20 =>
      -- One of the premise coincides with the conclusion.
      exact h20
    case inr h21 =>
      -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
      have h22 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h21, we can now drive its conclusion.
      let h23 := h21 h22
      -- We need to get the right conjuct of h23 based on <expert-advice>.
      let h24 := h23.right
      -- False on the left can always be used.
      apply False.elim h24
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350973025827776722056197937174 : (p4 → (((p2 ∨ (p2 → (p3 → p1))) → (((True ∧ (p1 ∨ p3)) ∨ ((p5 ∧ (p5 ∧ p2)) ∨ (p5 ∨ (False → False)))) ∧ p5)) ∨ (p2 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689284838453496795524008235164 : ((((((True → (((p4 ∧ (p1 ∨ p3)) ∨ True) ∧ (p5 ∨ p4))) ∨ p1) ∧ (p5 ∧ False)) ∨ (True ∨ ((p3 ∨ ((p3 ∧ p4) ∧ p2)) ∧ True))) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_66205134282696474009105820930 : ((p5 ∨ ((((p4 ∧ ((p2 ∧ p3) → p2)) → p5) → (True → ((p4 → p4) → p4))) ∨ (p4 ∨ (True → (p4 → ((False ∨ p5) ∨ p4)))))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43040310120627018098272067478 : ((((((p1 ∧ p5) ∨ (True → (p2 → (True → (p4 ∨ ((p3 ∨ (p3 ∨ p2)) ∧ ((p2 → p3) ∧ (p5 ∨ p3)))))))) ∨ p5) ∧ True) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177634752463951346502817812794 : ((((((p1 ∨ (p4 → False)) → p4) → (p3 → (p5 ∧ p5))) ∧ p5) ∧ p4) ∨ ((((p4 ∨ True) → p3) ∨ True) ∧ ((p5 ∨ (True → p1)) → True))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_779401409733512773042787475125 : (((p2 ∨ (((p1 ∧ ((((((p2 ∨ False) ∨ (p4 ∨ p4)) → (p2 → (p1 → ((p3 ∧ p4) → p2)))) ∨ p2) ∨ True) → p2)) ∨ p2) ∨ True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_266205990957802424546554070752 : (True ∧ (p4 → (((p3 ∧ (p4 ∨ False)) ∧ (False → (p5 → p3))) → (((True ∨ p2) → (p3 → (False ∧ p5))) → (False ∧ ((p5 → p2) ∧ False)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h9 : (True ∨ p2) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h10 := h3 h9
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h11 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h12 := h10 h11
    -- We need to get the left conjuct of h12 based on <expert-advice>.
    let h13 := h12.left
    -- False on the left can always be used.
    apply False.elim h13
  case inr h14 =>
    -- False on the left can always be used.
    apply False.elim h14
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h15
  -- Conjunctions on the left can always be decomposed.
  let h16 := h2.left
  let h17 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h18 := h16.left
  let h19 := h16.right
  -- Disjunctions on the left can always be decomposed.
  cases h19
  case inl h20 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h21 : (True ∨ p2) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h22 := h3 h21
    -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
    have h23 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h18
    -- We have shown the premise of h22, we can now drive its conclusion.
    let h24 := h22 h23
    -- We need to get the left conjuct of h24 based on <expert-advice>.
    let h25 := h24.left
    -- False on the left can always be used.
    apply False.elim h25
  case inr h26 =>
    -- False on the left can always be used.
    apply False.elim h26
  -- Conjunctions on the left can always be decomposed.
  let h27 := h2.left
  let h28 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h29 := h27.left
  let h30 := h27.right
  -- Disjunctions on the left can always be decomposed.
  cases h30
  case inl h31 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h32 : (True ∨ p2) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h33 := h3 h32
    -- We want to use the implication h33 based on <expert-advice>. So we show its premise.
    have h34 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h29
    -- We have shown the premise of h33, we can now drive its conclusion.
    let h35 := h33 h34
    -- We need to get the left conjuct of h35 based on <expert-advice>.
    let h36 := h35.left
    -- False on the left can always be used.
    apply False.elim h36
  case inr h37 =>
    -- False on the left can always be used.
    apply False.elim h37



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157253724473330099563762443692 : ((((False ∧ (p3 ∨ (p5 ∨ (p4 ∧ True)))) → ((False ∨ (p5 → True)) → (p5 → (p2 → p2)))) → p3) ∨ (((p5 ∧ p1) ∧ p5) → (p5 ∨ p5))) := by
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
theorem thm_5_vars_47384284554241448144136395953 : ((((p2 ∨ p4) → ((((p2 ∨ (p2 ∧ ((p2 ∧ False) ∧ ((p4 → True) ∧ False)))) ∨ ((True ∨ True) ∨ True)) ∧ p3) → False)) ∨ (False → True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_874763174635043215043327370544 : (((((p1 ∨ (True ∧ (((p3 ∧ (p2 ∨ p5)) ∨ p5) → (p5 ∧ (p1 ∨ ((p3 → (p5 → (p5 ∧ p1))) ∧ p1)))))) ∧ p5) ∧ (p1 → p2)) → p1) ∧ True) := by
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
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : ((p3 ∧ (p2 ∨ p5)) ∨ p5) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h11 := h9 h10
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- One of the premise coincides with the conclusion.
      exact h16
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_675495669034928217913166455376 : (((((p1 → (((p3 ∨ (p3 → p5)) ∧ (p4 → p5)) ∧ (((p2 ∧ (p3 → False)) → p2) → p3))) → p1) ∧ (((p5 ∨ False) ∨ False) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149311547534169656831203561672 : (((p2 ∧ True) → ((((p3 ∧ (p4 ∧ (False ∧ (p3 ∧ p2)))) ∧ (False → (p3 → p4))) ∧ p4) ∨ (p2 ∧ p1))) ∨ ((p3 ∨ True) ∧ (True ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157407378806406740496167573796 : ((((((False → p1) → (p4 ∨ p1)) → ((p4 → True) ∧ False)) ∨ ((p1 → False) → p5)) ∧ (True ∧ p5)) ∨ (p5 ∨ ((p4 ∧ p5) ∨ (p2 → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37769183072207190969881248824 : (((((p3 → (p5 ∨ p4)) ∨ (((((p1 ∨ p4) → ((p4 ∨ (False → p4)) → True)) ∨ (p3 ∨ p1)) → (p5 ∧ False)) ∨ p4)) → p4) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174916155363602679471409609711 : (((p2 ∨ p4) → ((p3 → p1) ∧ ((True ∧ (p3 ∧ p3)) ∨ ((p4 ∧ p5) → True)))) → ((p1 → p5) ∨ (p2 → (p1 → (p1 ∧ (p4 ∨ p2)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148388155226064074081734611002 : (((((p2 → p3) → p4) → (True ∧ ((((False → p4) ∨ False) → p2) ∨ True))) ∨ (p2 ∨ (p2 → (False → p2)))) ∨ ((p1 ∨ True) ∧ (p5 ∧ False))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_754883252114217960609748217191 : (((False ∧ (p3 ∨ ((((p3 ∨ False) → ((p2 ∧ True) → p2)) ∧ ((p3 ∨ ((p3 ∧ p5) → ((p1 ∨ p3) ∧ p2))) ∧ (True → p1))) ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702657145028273819238701813820 : (((((((p1 ∧ p1) → True) ∧ (p4 ∨ p1)) ∧ (p1 ∨ p2)) ∨ (p4 ∧ ((True ∨ (True → p2)) ∨ ((((p5 ∨ p5) → p4) ∧ p2) ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193753833110879753521444745362 : ((p3 ∧ ((p1 ∨ (p4 ∨ p5)) ∧ ((p5 ∨ False) ∨ p5))) → (((False → False) → p2) ∨ (True → (p1 → ((False → p1) ∨ ((p1 → p4) ∨ True)))))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h9
        -- Implications on the right can always be decomposed.
        intro h10
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h11 =>
        -- False on the left can always be used.
        apply False.elim h11
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- Implications on the right can always be decomposed.
      intro h14
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h17 =>
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h18 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h19
          -- Implications on the right can always be decomposed.
          intro h20
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h21 =>
          -- False on the left can always be used.
          apply False.elim h21
      case inr h22 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h23
        -- Implications on the right can always be decomposed.
        intro h24
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h25 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h26 =>
        -- Disjunctions on the left can always be decomposed.
        cases h26
        case inl h27 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h28
          -- Implications on the right can always be decomposed.
          intro h29
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h30 =>
          -- False on the left can always be used.
          apply False.elim h30
      case inr h31 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h32
        -- Implications on the right can always be decomposed.
        intro h33
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307327740992222441332636114108 : (p1 ∨ (p3 ∨ ((p2 ∨ ((p4 ∨ (p4 → (p4 → False))) ∨ True)) → ((p2 → (((False ∨ ((p4 → (p1 ∨ False)) ∨ p3)) ∨ True) ∨ p1)) ∨ p4)))) := by
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
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h7 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h8
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h10
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139025144867671021877789787342 : (((((((p2 ∧ (p4 ∧ ((False → (True ∧ (p3 ∨ (False ∨ p3)))) ∧ p1))) ∧ True) ∨ (False → True)) ∨ p4) → p1) ∨ p5) → ((p4 → p3) ∨ True)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179121599581507081879830982765 : ((p1 ∧ ((True ∧ ((False ∧ p1) ∨ ((p5 → (p1 ∨ p5)) → p5))) ∨ p2)) ∨ ((p3 → ((p3 ∨ (p3 ∧ p4)) ∨ p5)) ∨ (p2 ∨ (p5 ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57846400656851584191351284424 : (((True ∨ (True ∧ p5)) → (p1 ∧ ((((p3 ∧ True) → False) → (p4 ∧ ((((False ∨ p2) → p3) → (p3 ∨ p5)) ∧ (True ∧ False)))) ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67635331251740919019624672597 : ((p1 → (False ∨ (((((p5 → p1) ∧ (True → True)) ∨ ((p3 → p5) → (p4 ∨ (True ∧ (True ∨ (p1 ∨ True)))))) → p5) ∧ (p2 ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158355267528546227917777862485 : (((True ∨ p5) ∧ (p3 ∧ (p1 ∨ ((((((p2 → p4) → p1) ∧ (False ∧ p5)) → p5) ∧ p2) → p1)))) ∨ (p2 → (((p4 → p1) ∧ True) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157003680617635403371200187557 : (((((False ∨ p5) ∧ p2) ∧ (p2 ∧ (((((p1 → p1) ∧ True) ∨ (False ∧ p1)) → p5) ∧ False))) ∨ p1) ∨ (p1 → (((p1 ∧ False) ∨ True) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135543843378305828659340400387 : (((((p3 ∨ False) ∧ (p3 → p3)) ∧ ((((False → p5) ∧ (p3 → False)) ∨ p5) ∨ p4)) ∧ ((p3 ∨ True) ∧ (p3 → p4))) ∨ ((p5 ∨ True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678036622933739711682204812074 : (((((((((True ∧ p3) ∧ p5) ∨ (p5 ∧ True)) → (p5 → p3)) ∧ (p5 → p2)) ∨ (p5 ∨ (False ∨ p1))) ∨ (p2 → (p5 → (p1 ∨ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227678363555092838836727134898 : ((False ∧ (p4 → p2)) ∨ ((p5 → True) → ((((p5 ∧ (False ∧ (p1 ∨ False))) ∨ p4) → (p2 → ((p2 ∧ p3) ∧ p2))) ∨ ((p3 → False) ∨ True)))) := by
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
theorem thm_5_vars_653988764333902638841763308613 : (((((p4 ∧ (((((p4 ∧ p2) ∧ ((p1 → (p2 ∨ False)) ∨ p2)) ∨ p2) ∧ p5) ∧ (False ∨ ((True → p2) ∧ p1)))) ∧ True) ∨ (p4 ∨ True)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_340891841321731038088258864958 : (p2 → (((False → (((p3 ∧ True) ∧ (True ∧ True)) ∧ (p1 ∧ ((False ∧ p2) ∧ p5)))) → (p3 → ((p2 ∧ (True → (p3 ∨ p3))) ∧ p2))) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217096838113201558143153071128 : ((((p3 ∧ p4) ∨ False) ∨ p3) → ((((p2 ∧ p2) → (((p5 → p1) ∧ p5) ∧ False)) ∨ p4) → (p1 ∨ ((p2 → p4) ∨ (p3 ∧ (p4 → p4)))))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Conjunctions on the left can always be decomposed.
        let h6 := h5.left
        let h7 := h5.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h8
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h9 =>
        -- False on the left can always be used.
        apply False.elim h9
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h10
      -- Implications on the right can always be decomposed.
      intro h11
      -- One of the premise coincides with the conclusion.
      exact h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h17
        -- One of the premise coincides with the conclusion.
        exact h16
      case inr h18 =>
        -- False on the left can always be used.
        apply False.elim h18
    case inr h19 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h20
      -- One of the premise coincides with the conclusion.
      exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_922644759737939278263249626404 : ((((True ∨ (((False ∨ (p3 ∨ p4)) → p5) ∧ (((p5 ∧ p3) ∧ True) ∨ False))) → (((True ∧ (True ∨ p5)) ∧ False) ∧ (p2 ∨ (p4 ∨ p4)))) → False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ (((False ∨ (p3 ∨ p4)) → p5) ∧ (((p5 ∧ p3) ∧ True) ∨ False))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47266408016460362095980013465 : ((((((p3 ∨ True) ∧ p2) ∨ p3) ∧ (p3 ∨ (p5 ∨ ((p4 → p4) → (((p3 → False) ∨ p1) → (p3 → (p5 ∧ p3))))))) ∨ (p3 → p3)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231243969071804526120229668882 : (((p4 ∨ p1) ∨ p3) → ((p4 ∧ ((((p2 ∧ p5) ∨ p1) ∨ p2) ∧ (p5 ∨ (((p5 → p4) ∧ p4) ∧ (p4 → p5))))) → ((p3 → p1) → p5))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h13 =>
          -- Disjunctions on the left can always be decomposed.
          cases h13
          case inl h14 =>
            -- One of the premise coincides with the conclusion.
            exact h12
          case inr h15 =>
            -- One of the premise coincides with the conclusion.
            exact h12
        case inr h16 =>
          -- One of the premise coincides with the conclusion.
          exact h12
      case inr h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- Conjunctions on the left can always be decomposed.
        let h20 := h18.left
        let h21 := h18.right
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h22 =>
          -- Disjunctions on the left can always be decomposed.
          cases h22
          case inl h23 =>
            -- One of the premise coincides with the conclusion.
            exact h11
          case inr h24 =>
            -- One of the premise coincides with the conclusion.
            exact h11
        case inr h25 =>
          -- One of the premise coincides with the conclusion.
          exact h11
    case inr h26 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h27 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h28 =>
          -- Disjunctions on the left can always be decomposed.
          cases h28
          case inl h29 =>
            -- One of the premise coincides with the conclusion.
            exact h27
          case inr h30 =>
            -- One of the premise coincides with the conclusion.
            exact h27
        case inr h31 =>
          -- One of the premise coincides with the conclusion.
          exact h27
      case inr h32 =>
        -- Conjunctions on the left can always be decomposed.
        let h33 := h32.left
        let h34 := h32.right
        -- Conjunctions on the left can always be decomposed.
        let h35 := h33.left
        let h36 := h33.right
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h37 =>
          -- Disjunctions on the left can always be decomposed.
          cases h37
          case inl h38 =>
            -- We want to use the implication h34 based on <expert-advice>. So we show its premise.
            have h39 : p4 := by
              -- One of the premise coincides with the conclusion.
              exact h38
            -- We have shown the premise of h34, we can now drive its conclusion.
            let h40 := h34 h39
            -- One of the premise coincides with the conclusion.
            exact h40
          case inr h41 =>
            -- We want to use the implication h34 based on <expert-advice>. So we show its premise.
            have h42 : p4 := by
              -- One of the premise coincides with the conclusion.
              exact h36
            -- We have shown the premise of h34, we can now drive its conclusion.
            let h43 := h34 h42
            -- One of the premise coincides with the conclusion.
            exact h43
        case inr h44 =>
          -- We want to use the implication h34 based on <expert-advice>. So we show its premise.
          have h45 : p4 := by
            -- One of the premise coincides with the conclusion.
            exact h36
          -- We have shown the premise of h34, we can now drive its conclusion.
          let h46 := h34 h45
          -- One of the premise coincides with the conclusion.
          exact h46
  case inr h47 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h48 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h49 =>
        -- Disjunctions on the left can always be decomposed.
        cases h49
        case inl h50 =>
          -- One of the premise coincides with the conclusion.
          exact h48
        case inr h51 =>
          -- One of the premise coincides with the conclusion.
          exact h48
      case inr h52 =>
        -- One of the premise coincides with the conclusion.
        exact h48
    case inr h53 =>
      -- Conjunctions on the left can always be decomposed.
      let h54 := h53.left
      let h55 := h53.right
      -- Conjunctions on the left can always be decomposed.
      let h56 := h54.left
      let h57 := h54.right
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h58 =>
        -- Disjunctions on the left can always be decomposed.
        cases h58
        case inl h59 =>
          -- We want to use the implication h55 based on <expert-advice>. So we show its premise.
          have h60 : p4 := by
            -- One of the premise coincides with the conclusion.
            exact h59
          -- We have shown the premise of h55, we can now drive its conclusion.
          let h61 := h55 h60
          -- One of the premise coincides with the conclusion.
          exact h61
        case inr h62 =>
          -- We want to use the implication h55 based on <expert-advice>. So we show its premise.
          have h63 : p4 := by
            -- One of the premise coincides with the conclusion.
            exact h57
          -- We have shown the premise of h55, we can now drive its conclusion.
          let h64 := h55 h63
          -- One of the premise coincides with the conclusion.
          exact h64
      case inr h65 =>
        -- We want to use the implication h55 based on <expert-advice>. So we show its premise.
        have h66 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h57
        -- We have shown the premise of h55, we can now drive its conclusion.
        let h67 := h55 h66
        -- One of the premise coincides with the conclusion.
        exact h67



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113468884769686717903717935516 : ((((False ∨ (True ∨ ((p1 → True) → ((p1 ∨ p2) ∨ ((p1 ∨ p5) ∧ ((p3 ∨ p2) → (False ∧ True))))))) → p1) ∨ (False → p3)) ∨ (p5 ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43473234601182104755981157717 : ((((True ∧ (((p2 → (p1 ∧ p3)) → (False → (p5 ∧ p2))) ∨ (((False → p5) ∨ (p3 ∧ True)) ∨ (p4 ∧ (p5 ∧ True))))) ∨ p5) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_20917734124801713315596881261 : (((p3 ∧ (((p2 ∨ (p5 → (True ∧ p1))) → p5) ∨ (p5 ∨ True))) ∨ (True ∨ ((((p5 → (p5 ∨ p1)) → True) ∨ (p4 ∧ p2)) ∧ False))) ∧ True) := by
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
theorem thm_5_vars_308318610796895355242663040565 : (p2 ∨ ((p4 → ((p3 ∨ (((p4 ∨ (False ∧ False)) → ((p5 ∧ p5) ∨ p3)) ∨ True)) ∧ ((p5 → p4) ∨ (p2 → (p4 → (False ∧ p1)))))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621270567736112832064925499731 : ((((True ∧ ((p3 → (((((p1 ∨ True) ∧ (p1 ∨ p1)) → (p5 ∧ (p1 → p1))) ∨ False) ∨ (p5 ∨ p3))) → (p2 ∨ (p5 ∧ p2)))) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_53431532535740638335325177972 : (((((p1 ∧ p5) → (p2 ∨ p1)) ∨ ((p2 ∧ p2) ∨ (p3 ∨ p1))) → ((p5 → ((p2 ∧ (p3 ∧ p5)) ∧ True)) ∨ ((p2 → p5) → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219603397874978119818165804738 : ((True → (True → (False ∧ p3))) → ((p3 ∧ (p3 ∧ ((p5 ∨ p2) ∨ ((((False ∧ p2) ∧ p5) ∨ (p1 → False)) ∨ (p5 ∨ True))))) ∨ (p3 ∧ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668514335663022116391218018658 : ((((((((((p3 ∧ p2) ∨ p3) → p3) → True) → (False → p5)) ∧ (((p1 ∧ p1) ∨ (p2 → p3)) ∨ p4)) ∧ p2) ∨ ((True ∧ False) → p5)) ∨ False) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47861401738464635859810390293 : (((((True ∧ ((True → p2) → ((p3 ∨ ((p1 ∨ p3) → (p1 → (p1 → (p2 ∧ p5))))) ∨ p2))) ∨ True) ∧ (True → p3)) → (p2 ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614663726212607400744151214660 : (((((((((p2 → (((False → p3) → p1) ∨ False)) ∧ p3) ∧ p5) ∨ ((p1 ∧ False) → p1)) ∧ p5) ∨ ((True ∨ p1) ∨ (False → False))) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_650005533076638286515181483164 : (((((p1 ∧ (((p1 ∨ (p1 → ((p2 → False) ∧ False))) ∧ (True ∨ (p5 ∨ (p1 ∨ p4)))) ∨ p3)) ∨ (True ∨ (p3 → p1))) ∧ (False → p2)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51995505574030062511719636168 : (((True ∧ (((p5 → p1) ∧ ((p1 ∧ (p5 ∧ ((p4 → p5) → p5))) ∧ p1)) ∧ p5)) ∨ ((True → (((p4 ∧ p2) ∨ p4) ∧ p2)) → p2)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_106450363752109209205358122690 : (((((False → p3) → (p4 ∧ False)) → (p2 → p1)) ∧ (((p1 → False) → p4) ∨ (p3 → ((p5 ∨ ((p4 → p3) → p2)) ∨ p3)))) ∧ (False → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (False → p3) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h3
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h7
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46973723285653889772725353193 : ((((((p4 ∨ True) → (((p1 ∨ p2) ∨ ((True ∧ (False → (p3 → (p3 ∨ True)))) ∧ (p5 → p3))) → p3)) → True) → False) ∨ (p1 ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191839063725132928285634974304 : ((p3 ∨ (((False ∧ p1) ∧ p5) ∨ (p2 ∧ (p2 ∨ True)))) ∨ (False → (p1 ∧ (p4 ∧ (p4 ∨ ((p4 ∨ p4) → (((False → p5) ∨ p3) → True))))))) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135440257291442578973099544795 : (((p5 → ((p5 ∧ p3) ∨ ((p3 → ((False → ((p3 ∧ False) → (False ∨ p1))) ∨ True)) → p4))) ∨ ((p3 ∨ True) ∨ p2)) ∨ ((p3 ∧ False) → p5)) := by
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
theorem thm_5_vars_344859938759224578243657243864 : (p2 → (p5 → ((((True ∨ (True ∧ False)) → p3) → True) → ((p3 ∨ (p2 → (p3 ∧ p3))) → (((p1 ∨ p2) → (p4 ∨ (p3 ∧ p3))) ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199950776885465866076622750152 : (((p1 ∨ ((True ∨ True) → True)) ∨ (p4 ∧ p5)) → (True → (((p4 ∧ (p2 ∧ p5)) → ((p2 ∧ False) ∨ (p4 ∨ p2))) ∧ ((p3 ∨ True) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h12
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h16 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38883491148150841692120081734 : (((((p5 → p2) ∧ True) ∨ ((((((p4 ∧ (True → p4)) ∨ p4) → p4) ∧ (p2 ∨ p2)) ∨ p4) → (p5 ∧ ((p4 ∧ p2) → p2)))) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208288134574960708370109104247 : (((p2 ∨ p2) ∧ (p3 → (p2 ∨ p4))) → (False ∨ ((p1 → ((p5 ∨ p1) ∨ ((p5 ∧ p2) → (False ∨ p4)))) ∧ ((p3 → (p1 ∧ True)) ∨ p2)))) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_688246221168167783509715373872 : (((((p5 → p4) ∧ (False ∨ (False ∧ (p4 ∧ (p3 ∧ (((p4 → True) ∧ p5) ∨ True)))))) ∧ (((p1 → (True → (p4 ∨ False))) ∧ p2) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257230769484671233899202727911 : ((p2 ∨ p2) → (p3 ∨ ((((p5 ∧ p2) ∨ False) ∨ (False → p2)) ∨ (p5 → (((p4 ∨ (False ∧ (p1 ∨ (False ∧ p3)))) → False) ∧ (p5 → p3)))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149163531355249517210420825686 : (((p3 ∨ p4) ∧ ((p5 ∨ (p5 → ((((p3 ∨ p2) ∨ p3) ∨ p3) ∧ False))) → (p5 ∨ (p2 → (p1 ∧ p3))))) ∨ (p5 → ((False ∨ p1) → p1))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57750930169324693279982004312 : ((((p1 → False) → True) → ((((p1 ∨ (p1 ∧ ((p2 → False) ∨ ((p5 → False) → p2)))) ∧ (True ∧ p2)) ∧ True) ∨ ((False ∨ True) ∨ p2))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_49986154526281141871656018419 : (((((((p1 ∨ ((True ∨ p2) ∨ p2)) ∧ p4) ∧ (p2 → True)) ∧ p5) → (((p5 ∧ p3) ∨ p1) ∨ p4)) ∧ (((p5 ∧ p4) → p4) → True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
  -- Implications on the right can always be decomposed.
  intro h14
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111846015768449877104367593673 : ((((((((p3 ∨ p3) ∨ (p1 ∧ True)) ∧ p4) ∨ (((p3 ∨ (p4 ∨ p1)) ∧ p4) ∧ p1)) ∨ True) → ((p5 ∨ True) ∨ False)) ∨ False) ∨ (p3 → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Conjunctions on the left can always be decomposed.
      let h4 := h3.left
      let h5 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h8 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Conjunctions on the left can always be decomposed.
      let h15 := h13.left
      let h16 := h13.right
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h17 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h20 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
  case inr h21 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166410616956174968174252600032 : ((p1 ∨ ((((p4 → (False ∧ p1)) ∧ p2) ∨ (p1 → ((p2 ∨ True) ∨ (p2 ∨ False)))) ∨ False)) ∨ (((p4 → False) ∨ (p4 ∨ p5)) → (p2 ∧ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_782716848490725090820995588982 : (((p3 ∨ ((((p3 → ((((p2 ∨ p1) → p3) ∧ p1) ∧ (p1 → p2))) ∧ (p4 ∧ (p1 ∧ (p5 ∧ p1)))) → (True ∧ (p2 ∧ p4))) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197459336952092015326672976198 : (((((p3 ∧ p1) → p4) → False) ∧ (False ∧ p2)) ∨ ((p5 → p5) ∧ (False → ((p4 ∨ ((True ∧ False) ∧ ((p2 ∧ True) ∨ p5))) ∨ (p1 ∧ p4))))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53738638395167649415461848844 : (((p4 → ((((p5 ∨ p5) ∨ p1) → False) ∨ (p3 → False))) ∧ ((p4 ∧ p1) → (False ∧ ((p4 → ((p1 ∧ p3) ∧ True)) ∧ (p3 ∧ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_700635015041689288796291638806 : ((((p2 → (False → ((p1 ∨ p4) ∨ ((p2 ∧ (p1 ∨ p5)) ∨ p4)))) → ((p2 ∧ p1) → (((True ∨ (True ∧ p3)) → False) ∨ (p1 ∨ False)))) ∨ p3) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622203013746994062895646382213 : ((((p2 ∧ (p4 ∧ (((((((p2 ∧ p1) → (p5 ∧ ((p4 ∨ (p4 ∨ False)) ∨ p1))) ∨ (p3 ∧ p4)) → p2) → p3) ∧ True) ∨ False))) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219624156854602329950240997336 : ((False → ((p3 → p4) ∧ p2)) → ((((((False ∧ p4) ∧ False) ∨ (p5 → p2)) ∨ p1) ∨ True) ∨ (((p1 ∧ p4) → (p2 ∧ p2)) ∧ (True ∧ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221466913998488041700787169234 : (((False → p5) ∨ p5) ∧ ((p2 ∨ (True → ((((((p1 → ((p5 → p1) → p2)) ∨ p5) ∨ p1) ∨ p1) ∨ (p3 ∨ True)) ∧ p1))) ∨ (p1 ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328978968569249583236363325167 : (True → (((((p4 ∨ p5) ∧ p1) ∧ p3) ∨ p3) ∨ ((p3 ∧ ((True → (False ∧ ((p2 ∧ p2) ∨ (p2 → (p5 ∧ p3))))) ∨ p4)) → (p4 ∨ False)))) := by
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
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h7 := h5 h6
    -- We need to get the left conjuct of h7 based on <expert-advice>.
    let h8 := h7.left
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_102741175235594237788043882669 : ((((p5 ∨ (((((p5 ∨ (p5 ∨ (p2 → (((p5 → (False ∨ p1)) ∧ False) ∧ False)))) → p3) ∨ p4) ∧ p5) ∧ True)) ∨ True) ∨ False) ∧ (p4 → True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_652928607534119141181626592265 : ((((p4 ∨ (p4 ∧ ((p4 ∧ ((((p5 ∨ (p2 ∨ p3)) → p2) → (False → p4)) ∨ p1)) ∧ (((p1 → False) ∧ True) ∨ False)))) ∧ (p1 ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156648857610917589946154422917 : (((((p5 ∧ (((True ∨ (True → True)) ∧ (p5 ∧ (p1 ∧ (p3 ∧ False)))) ∧ True)) → p2) → p4) ∧ False) ∨ (p4 → ((p5 ∨ (p3 → p5)) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136360259449020437991357399223 : ((((p3 ∧ (True ∧ p3)) ∧ p3) ∨ (p5 ∨ (p5 ∧ ((((p3 → p5) ∧ (((p3 ∧ p5) ∨ True) ∧ p2)) ∧ p3) ∧ p5)))) ∨ ((False → p5) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53983002288526451278951397004 : (((((p1 ∨ (((p2 → False) → p5) ∧ p3)) → False) ∨ p5) → ((p4 ∨ p5) ∧ (False ∧ ((p1 → (p3 → (p5 ∨ p4))) ∨ (p4 ∧ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244508245943283702489401813312 : ((False ∧ p3) ∨ (((p5 → p3) → ((True ∨ p4) ∧ ((((p5 ∨ p5) ∧ (True ∧ ((p3 → p1) ∨ p5))) ∧ p3) ∨ True))) ∨ ((p1 ∨ True) → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_45966123575141838603437340515 : (((p5 → (True ∨ ((p4 ∨ ((p3 ∨ (p4 ∧ p1)) ∧ True)) ∨ (p3 ∨ (False ∨ (((((p2 ∨ p4) ∧ p1) ∨ p1) → False) ∨ p5)))))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135590481492731775703740168019 : (((((False ∧ ((p1 ∧ True) ∧ (False → p4))) ∧ (p5 ∧ True)) ∧ (p4 → (p2 ∨ p3))) ∨ (p3 ∨ (False ∨ (False → True)))) ∨ ((p2 ∧ True) ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_46545035629726789752399006778 : ((((p4 → p2) ∨ (p5 ∨ (p2 ∨ ((p2 → (p4 ∧ (((False ∨ True) → (p3 ∧ ((False ∧ p2) ∨ p3))) ∧ False))) ∨ p3)))) ∧ (p2 ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_597238246753511234908375290098 : ((((((p2 → False) ∧ (p4 → p3)) ∧ ((True → p2) ∨ (((((p2 ∧ p3) → True) ∨ ((p2 ∨ p5) ∨ p4)) ∧ p4) ∨ (p5 ∨ False)))) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217209012392853968557685839308 : ((((True → False) → p5) ∨ p4) → (((False → p1) ∨ p5) ∧ ((p5 → p2) → ((p5 → (False ∨ ((p3 ∨ (p4 ∨ p3)) ∧ p4))) ∨ (True → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114867665871048101273136909965 : ((((False ∧ (((False ∧ True) ∨ p3) ∨ False)) ∧ ((p3 → True) ∨ (p5 ∨ True))) ∨ (p5 → ((((p3 ∧ p1) ∧ p4) ∧ True) ∨ p1))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322248892686752272048659101454 : (p5 ∨ (((((False ∨ (p2 → ((((True ∨ False) → p4) ∧ p5) → (p2 ∨ ((p3 ∧ p2) ∧ (p1 → True)))))) ∧ p5) → (p5 ∧ False)) ∨ True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138369971626847634033498167282 : ((p4 → ((((p4 ∨ (p4 → p5)) ∧ (p4 → False)) ∧ (True ∨ p3)) → ((((p1 ∨ (p4 ∨ p3)) → p1) → p1) ∨ True))) ∨ (p5 → (p4 ∨ False))) := by
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
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
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
theorem thm_5_vars_232816936578333806428965503437 : ((p2 ∧ (p1 ∨ p1)) → ((p3 ∨ ((False ∨ ((p2 ∧ p2) ∨ p2)) ∧ p4)) ∨ (((False → True) ∨ (p5 ∨ (p2 → False))) ∧ (False → (False ∨ False))))) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h8
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h9
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119542106788068374826613011368 : ((p5 → (((((p5 → (False ∧ True)) ∨ (((p4 ∨ True) ∧ ((True ∨ p4) ∧ p3)) ∨ False)) ∨ p4) ∧ (p5 ∨ p5)) ∨ (False → p2))) ∨ (p5 ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303872455692159597080849221188 : (p1 ∨ (((p1 ∧ (p4 ∧ ((p4 ∨ ((p5 → True) ∨ (True ∧ (p2 ∨ p3)))) → ((True ∨ (p1 ∨ p3)) ∧ p5)))) → (p1 → (p1 ∧ p5))) ∨ p5)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
  have h11 : (p4 ∨ ((p5 → True) ∨ (True ∧ (p2 ∨ p3)))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h10, we can now drive its conclusion.
  let h12 := h10 h11
  -- We need to get the right conjuct of h12 based on <expert-advice>.
  let h13 := h12.right
  -- One of the premise coincides with the conclusion.
  exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324108690380982233532001475401 : (p5 ∨ ((((p2 ∨ (p4 ∨ (p5 ∨ p3))) ∨ (False → False)) → (False ∧ p1)) → ((p1 → ((p5 ∧ False) ∨ ((p2 ∧ p5) ∨ (p4 → p1)))) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p2 ∨ (p4 ∨ (p5 ∨ p3))) ∨ (False → False)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320270909175345820830213941649 : (p4 ∨ ((False ∧ p5) ∨ (p5 ∨ (((p5 ∨ (False ∧ (p3 → (p2 ∧ (p2 → (((p2 → True) ∧ (p2 ∧ (p2 ∧ False))) ∨ False)))))) ∨ True) ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_179721799180936585159001319249 : (((((((True → (p1 ∨ True)) ∨ p4) ∧ p5) ∨ (p4 → False)) → True) ∧ p4) → (p2 ∨ ((p2 ∧ (False ∨ ((False ∨ p5) ∨ p2))) ∨ (False → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322556140063131527971291973085 : (p5 ∨ ((p1 ∨ (((p1 → p3) ∧ ((p4 ∨ (p5 ∨ (((True ∧ ((p3 ∨ p2) → False)) ∧ p5) ∧ False))) → False)) ∨ ((True ∨ p5) → False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52242390353149283615061909009 : (((p5 ∧ ((((False → ((p5 ∨ p2) → False)) ∧ p4) → ((False ∨ p5) ∧ p1)) → p1)) → ((p1 ∨ True) ∨ (p1 ∨ (p3 → (p2 ∨ p1))))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48270073266581200013801534713 : (((p3 ∧ (((p1 ∧ p1) ∧ ((((p2 ∧ p1) ∨ p1) ∨ p1) ∨ (((p3 ∨ p5) ∨ p1) ∨ p1))) → ((p5 → p1) → p4))) → (True ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174965403175755589943205844884 : ((True ∧ ((p1 ∨ p2) ∧ (p5 → (((p3 → p1) ∨ ((p5 ∨ p4) ∧ p2)) ∨ False)))) → ((p3 ∨ ((p5 ∨ p5) ∧ (p4 ∨ (p1 ∧ p5)))) ∨ True)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



