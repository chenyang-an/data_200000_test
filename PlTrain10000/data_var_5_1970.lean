variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118869729461302021144290874001 : ((True → ((p3 ∧ (p5 → True)) ∨ ((((False ∨ ((p3 ∨ (True ∨ (False → True))) → p1)) ∨ (p3 ∨ p1)) → p3) ∨ (p5 ∨ p5)))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_811230428607690206952539196277 : (((p5 → (p5 ∧ ((p5 ∧ ((((p3 ∧ ((p1 ∨ (p2 → ((p3 ∧ (False ∧ p2)) ∧ p1))) ∨ (p4 ∨ p5))) → p1) ∧ p1) ∧ False)) ∨ True))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316984967220481486828639659807 : (p3 ∨ (p3 → ((((p2 ∨ p5) → (((p2 → p5) ∧ ((p5 ∨ p5) ∨ True)) ∧ (True ∧ (True ∧ (p4 ∧ p2))))) ∨ (True → p1)) ∨ (p4 → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679755604038241630007766152138 : ((((((p2 → ((True ∨ p1) → ((True ∧ False) → False))) ∧ (True → (((p4 → False) → True) ∨ p4))) ∨ False) → (((True → True) → p2) → p2)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h6 : (True → True) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h6
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113693806154961017055689356742 : (((((False → ((p5 → (True → p4)) ∧ p3)) ∨ ((((p2 ∨ p3) ∨ p1) → p3) → ((p2 → p3) → p2))) → p4) → (p1 ∧ p3)) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_723526814267870003382882951522 : (((((True ∨ p5) → False) ∧ ((((((p1 ∨ (((p3 → p4) ∨ p4) ∧ p3)) → (p2 ∧ (p4 ∨ p5))) ∧ p3) ∨ (True ∧ p4)) ∨ p2) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_182862291720349873583917764967 : ((((p3 → p4) ∨ p5) ∨ ((True ∨ (p5 ∧ p4)) ∨ (p1 → p2))) ∧ (p5 ∨ (((True ∨ (p5 ∧ p4)) → (False ∧ p2)) ∨ (p3 → (p3 → True))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49528728539801235734880162663 : ((((((True ∨ (p1 ∨ False)) ∧ True) ∧ ((p3 ∨ (p3 → p3)) → ((p2 ∨ False) ∨ (p2 → False)))) ∨ (p2 ∨ p3)) → (p1 → (p2 ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174536713860284663917770972910 : ((((p5 ∨ False) ∨ ((p5 → p4) → p5)) → (((p4 → False) ∧ p3) ∨ (p2 ∨ True))) → ((p1 ∨ (False ∨ (p2 → p4))) ∨ (p1 → (p1 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197207733123309425829025670761 : ((((((p1 ∧ p2) ∧ p5) → p1) ∨ p3) → p2) ∨ (((p2 ∧ p3) ∨ (p2 ∨ ((p1 ∧ ((p2 ∧ False) → (p1 ∨ True))) → (True ∧ p2)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_106006497798162151590734269622 : ((((p5 → ((False → p5) ∨ (p1 ∨ (p3 → p1)))) → (p1 → (p5 → p2))) → (((p2 ∧ p1) ∧ True) ∨ ((False → True) ∨ False))) ∧ (False → False)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316491372482406358273254686005 : (p3 ∨ (p2 ∨ ((p5 → (((p1 → p2) ∨ (((p2 → (p2 ∧ p4)) → p2) → ((True ∨ True) ∧ p1))) ∨ (p1 → (p4 → (p3 → p5))))) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_752203779041031821484366243186 : (((True ∧ (p3 → ((((True ∨ p5) ∧ p5) → False) ∨ ((p2 → ((((True → p5) ∧ (p1 → (p4 ∨ p1))) ∨ p3) ∨ p3)) → (False ∨ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194086986038983468341563180449 : ((True → (p3 ∧ ((p1 → p1) ∨ ((p1 ∧ p2) → p3)))) → ((((p1 ∧ p2) ∨ (p3 → ((False → (p2 ∧ True)) ∨ (p5 → False)))) → p3) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h7 := h1 h6
    -- We need to get the left conjuct of h7 based on <expert-advice>.
    let h8 := h7.left
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h10 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h11 := h1 h10
    -- We need to get the left conjuct of h11 based on <expert-advice>.
    let h12 := h11.left
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_87293373437895371411688267383 : ((((p1 ∨ ((p4 ∨ p5) → True)) → False) ∧ (((True ∧ False) → (p2 ∧ p4)) ∧ ((True ∨ ((p3 → p2) ∨ ((p2 → p1) ∨ True))) ∨ p5))) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h8 : (p1 ∨ ((p4 ∨ p5) → True)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h9
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h10 := h2 h8
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h13 : (p1 ∨ ((p4 ∨ p5) → True)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h14
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h15 := h2 h13
        -- False on the left can always be used.
        apply False.elim h15
      case inr h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h17 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h18 : (p1 ∨ ((p4 ∨ p5) → True)) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h19
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h20 := h2 h18
          -- False on the left can always be used.
          apply False.elim h20
        case inr h21 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h22 : (p1 ∨ ((p4 ∨ p5) → True)) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h23
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h24 := h2 h22
          -- False on the left can always be used.
          apply False.elim h24
  case inr h25 =>
    -- One of the premise coincides with the conclusion.
    exact h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310546735160047406891560946834 : (p2 ∨ ((p3 ∧ (p3 ∨ ((p1 ∧ p2) → True))) → ((((p1 ∧ p3) → p3) ∧ ((((((p3 ∨ False) ∧ False) ∨ p2) → False) ∨ True) ∨ False)) ∧ p3))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  -- Conjunctions on the left can always be decomposed.
  let h9 := h1.left
  let h10 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h11 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h12 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h13 := h1.left
  let h14 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h14
  case inl h15 =>
    -- One of the premise coincides with the conclusion.
    exact h15
  case inr h16 =>
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234852783669820239231016622647 : ((p5 → (True → p1)) → (p3 ∨ (((((p5 → (p2 ∨ (p5 ∨ True))) ∧ False) ∧ (p1 ∧ p3)) ∨ True) ∨ (p5 ∨ (p3 → ((p4 → p4) ∧ p5)))))) := by
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
theorem thm_5_vars_214206524290915978929059354133 : ((((p1 → True) → True) → False) ∨ (((p3 ∨ False) → p3) → ((((False ∨ ((p1 ∨ (p2 ∨ p1)) → p1)) → p2) ∨ (p2 ∨ p2)) ∨ (True ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689344770648507234023191489473 : (((((((p4 → (p1 → p5)) ∨ False) ∧ ((p1 ∨ p1) ∨ (p4 ∧ p3))) ∨ (True ∧ True)) ∨ (((p5 ∧ ((p2 ∧ p1) ∧ p3)) ∨ p1) ∨ p2)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260274183699584622886676669296 : ((p2 → p3) → (p5 → ((p4 ∨ (((p1 ∧ p2) ∨ ((p5 → p2) → ((p4 ∨ p3) → (((p3 → p4) ∧ (False ∨ p5)) ∧ p3)))) ∨ True)) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_723957772228624664966180932168 : ((((False ∧ (p3 ∧ p2)) ∧ ((((p4 ∧ (False ∨ (False ∧ ((False → p4) ∧ p4)))) ∨ (p4 ∨ p2)) ∨ (p5 ∨ (True → True))) → (p1 ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112693855086495012302148195549 : (((((p3 ∧ ((p5 ∨ False) → (((p3 ∨ p2) ∧ (p1 → (True → True))) → p3))) ∨ p2) ∨ (p3 ∧ (p3 ∨ (p4 ∨ True)))) → p4) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184216545531015374044729204303 : ((((((False ∨ p1) ∨ ((p1 ∧ p5) ∧ False)) → True) ∨ p4) → False) ∨ ((False → False) ∨ (((p5 ∧ (((p1 ∧ p2) → p1) ∧ True)) ∧ p1) ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196858101242343355577160012270 : (((p2 ∨ ((p5 ∨ (p2 ∨ p4)) ∧ p2)) ∧ p4) ∨ ((p3 → (p1 ∧ p4)) → (((True ∨ p4) ∧ True) ∨ (p3 ∧ ((False ∧ p4) → (p2 ∧ p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321867263685134255530141045591 : (p5 ∨ ((((((True ∨ p1) ∨ (p3 → (p1 → ((False ∧ p5) ∨ (False → p1))))) → p1) ∧ ((p4 → p3) ∨ (p4 ∧ (p3 → False)))) → p1) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : ((True ∨ p1) ∨ (p3 → (p1 → ((False ∧ p5) ∨ (False → p1))))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h10 : ((True ∨ p1) ∨ (p3 → (p1 → ((False ∧ p5) ∨ (False → p1))))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h11 := h2 h10
    -- One of the premise coincides with the conclusion.
    exact h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_782450525919898990110842550070 : (((p3 ∨ ((((p1 → (p3 ∨ (True ∧ ((False ∧ False) ∨ (p3 ∧ (p2 ∨ (p1 ∧ p2))))))) → p3) → ((False → (p2 → p1)) ∧ p1)) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321267500433025463967720749523 : (p4 ∨ (p4 ∨ ((True ∨ False) → (((p4 ∧ (((((True ∨ (p3 → True)) → p3) ∨ False) ∨ (False → (p2 ∨ p5))) → False)) → p5) ∨ (p5 ∧ p4))))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : ((((True ∨ (p3 → True)) → p3) ∨ False) ∨ (False → (p2 ∨ p5))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- False on the left can always be used.
      apply False.elim h7
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h6
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191191456856159795229093283571 : ((((False → True) ∧ p2) → (p2 ∧ ((True → p3) ∨ False))) ∨ ((((p2 ∨ (False → p4)) ∧ (True ∨ True)) ∨ ((p5 → p1) ∧ (p3 ∧ p3))) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204465978898843563234835094503 : ((((True → (p5 → p5)) ∧ p2) ∨ p4) ∨ (((p5 ∧ p1) ∧ p2) ∨ ((p5 ∧ (False ∧ (p4 ∨ (p1 ∧ p5)))) → (p4 ∨ ((p5 ∨ p3) ∧ False))))) := by
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327844519713523901953370892750 : (True → (((((p5 ∨ (p1 ∨ (((p1 ∧ True) → p3) → True))) ∨ False) ∨ p4) → (True ∧ (True ∧ ((p4 ∧ p3) ∨ (p1 ∧ p2))))) ∨ (True → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314743323460717228674128714643 : (p3 ∨ ((((p3 ∨ p5) → ((p1 ∧ ((p5 → p4) → p2)) → False)) ∨ (p1 → p4)) ∨ ((p3 → (p3 ∧ ((True → False) → p4))) ∨ (True → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37992486927068936431452947720 : (((((p2 → (False ∨ (p5 ∧ (p2 → p2)))) → ((True ∨ (((p2 → p4) ∨ True) → (True ∨ (p1 ∧ p5)))) → p4)) ∨ (False → p3)) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184130216956571977177411593397 : (((p1 ∧ (p4 ∨ (False ∧ (((p1 → p3) ∧ p5) → p2)))) ∨ p5) ∨ (((p2 → ((p1 ∧ False) → p2)) ∨ p5) ∧ (True ∨ (p4 ∧ (p4 ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61642795223377597527231129700 : ((p1 ∧ (True ∧ (p5 → ((p5 ∨ ((((p3 ∧ ((((p3 → (True ∨ False)) ∨ p1) ∨ p3) → p5)) ∨ (False ∨ False)) ∧ p4) ∧ p2)) → False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352350948680851062799152461918 : (p4 → ((False ∨ (p1 ∨ True)) ∧ ((p5 ∨ (p2 ∨ (p1 ∨ ((True ∧ p1) → (p4 ∨ ((p5 → (True → p5)) ∧ True)))))) ∨ (p5 → (p1 ∨ p3))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232051699113837961084654444595 : (((p3 ∨ p5) → False) → (True → ((True ∧ (p1 ∨ ((p2 → p2) → (True → (((True ∧ p1) ∨ p3) ∧ p2))))) → (p1 ∨ ((p2 ∨ p4) ∨ False))))) := by
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
  cases h5
  case inl h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : (p2 → p2) := by
      -- Implications on the right can always be decomposed.
      intro h9
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h10 := h7 h8
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h11 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h12 := h10 h11
    -- We need to get the right conjuct of h12 based on <expert-advice>.
    let h13 := h12.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_16633306851575484855656462234 : ((((p5 ∧ (p2 ∧ ((((p5 → (p2 ∧ p3)) → p2) ∨ (((False ∨ True) ∨ p3) ∧ p3)) ∧ (True ∨ False)))) ∨ p3) ∨ (True ∨ (p1 ∨ p3))) ∧ True) := by
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
theorem thm_5_vars_205608870334731627123612178081 : (((True ∧ p2) ∨ ((p3 ∨ p4) ∨ False)) ∨ (False ∨ (False → ((p1 → (p1 → p1)) ∧ ((p4 ∧ (p5 ∧ p1)) ∧ ((True ∨ True) ∨ (p4 ∧ False))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721658644923320085879993066405 : ((((True ∨ (p2 ∧ (p2 ∧ p2))) → ((p1 ∨ (False ∨ p5)) ∨ ((((p5 ∨ p1) ∨ p5) ∧ False) → (p1 ∧ (False ∧ (p4 ∧ (False ∧ p5))))))) ∨ p3) ∧ True) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h10 := h3.left
    let h11 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- False on the left can always be used.
        apply False.elim h11
      case inr h14 =>
        -- False on the left can always be used.
        apply False.elim h11
    case inr h15 =>
      -- False on the left can always be used.
      apply False.elim h11
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h16 := h3.left
    let h17 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- False on the left can always be used.
        apply False.elim h17
      case inr h20 =>
        -- False on the left can always be used.
        apply False.elim h17
    case inr h21 =>
      -- False on the left can always be used.
      apply False.elim h17
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h22 := h3.left
    let h23 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h24 =>
      -- Disjunctions on the left can always be decomposed.
      cases h24
      case inl h25 =>
        -- False on the left can always be used.
        apply False.elim h23
      case inr h26 =>
        -- False on the left can always be used.
        apply False.elim h23
    case inr h27 =>
      -- False on the left can always be used.
      apply False.elim h23
    -- Conjunctions on the left can always be decomposed.
    let h28 := h3.left
    let h29 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h28
    case inl h30 =>
      -- Disjunctions on the left can always be decomposed.
      cases h30
      case inl h31 =>
        -- False on the left can always be used.
        apply False.elim h29
      case inr h32 =>
        -- False on the left can always be used.
        apply False.elim h29
    case inr h33 =>
      -- False on the left can always be used.
      apply False.elim h29
  case inr h34 =>
    -- Conjunctions on the left can always be decomposed.
    let h35 := h34.left
    let h36 := h34.right
    -- Conjunctions on the left can always be decomposed.
    let h37 := h36.left
    let h38 := h36.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h39
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h40 := h39.left
    let h41 := h39.right
    -- Disjunctions on the left can always be decomposed.
    cases h40
    case inl h42 =>
      -- Disjunctions on the left can always be decomposed.
      cases h42
      case inl h43 =>
        -- False on the left can always be used.
        apply False.elim h41
      case inr h44 =>
        -- False on the left can always be used.
        apply False.elim h41
    case inr h45 =>
      -- False on the left can always be used.
      apply False.elim h41
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h46 := h39.left
    let h47 := h39.right
    -- Disjunctions on the left can always be decomposed.
    cases h46
    case inl h48 =>
      -- Disjunctions on the left can always be decomposed.
      cases h48
      case inl h49 =>
        -- False on the left can always be used.
        apply False.elim h47
      case inr h50 =>
        -- False on the left can always be used.
        apply False.elim h47
    case inr h51 =>
      -- False on the left can always be used.
      apply False.elim h47
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h52 := h39.left
    let h53 := h39.right
    -- Disjunctions on the left can always be decomposed.
    cases h52
    case inl h54 =>
      -- Disjunctions on the left can always be decomposed.
      cases h54
      case inl h55 =>
        -- False on the left can always be used.
        apply False.elim h53
      case inr h56 =>
        -- False on the left can always be used.
        apply False.elim h53
    case inr h57 =>
      -- False on the left can always be used.
      apply False.elim h53
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h58 := h39.left
    let h59 := h39.right
    -- Disjunctions on the left can always be decomposed.
    cases h58
    case inl h60 =>
      -- Disjunctions on the left can always be decomposed.
      cases h60
      case inl h61 =>
        -- False on the left can always be used.
        apply False.elim h59
      case inr h62 =>
        -- False on the left can always be used.
        apply False.elim h59
    case inr h63 =>
      -- False on the left can always be used.
      apply False.elim h59
    -- Conjunctions on the left can always be decomposed.
    let h64 := h39.left
    let h65 := h39.right
    -- Disjunctions on the left can always be decomposed.
    cases h64
    case inl h66 =>
      -- Disjunctions on the left can always be decomposed.
      cases h66
      case inl h67 =>
        -- False on the left can always be used.
        apply False.elim h65
      case inr h68 =>
        -- False on the left can always be used.
        apply False.elim h65
    case inr h69 =>
      -- False on the left can always be used.
      apply False.elim h65
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312300747119078882550672668920 : (p2 ∨ (p2 → (((((True ∧ (p5 ∧ ((p3 ∨ p5) ∧ p4))) ∨ p3) ∨ (((p5 → True) ∨ (p3 ∨ p1)) ∧ (p1 ∨ p2))) ∧ p4) ∨ (False → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263587992226423300709774537129 : (True ∧ ((p5 ∨ ((True ∧ (((p4 → (p2 ∨ p1)) ∨ (p2 → p3)) ∧ (((False ∨ p5) → p4) → p2))) ∧ p2)) ∨ (p2 → (p2 ∨ (p2 → p1))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247728907726251448052378423253 : ((p1 ∨ False) ∨ ((((((p2 ∨ (p2 → p3)) ∨ False) ∨ ((p4 → p2) ∧ p1)) ∨ (p3 → p1)) ∨ (p5 ∨ p4)) ∨ (((p2 → False) → True) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_741163475988370774923249368724 : ((((p4 ∨ p1) ∨ ((True ∧ p3) → (((((p4 ∧ (p1 ∧ p2)) → p5) ∨ (((True ∨ (p3 ∨ p2)) ∧ False) ∨ p2)) ∧ p2) ∧ (p2 ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61829533469304660268850458006 : ((p2 ∧ ((p4 ∨ ((p3 → (p1 → (((p4 → False) ∨ True) ∨ ((p4 ∨ (True → p4)) → False)))) ∧ ((p2 ∧ (False ∨ False)) ∧ p2))) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_626064416195017722034085195334 : ((((p2 → (p5 ∧ ((p5 ∧ (((p5 ∨ (p2 → p5)) ∨ ((((True ∨ p4) ∨ p5) → ((p5 ∨ p5) → False)) ∧ p4)) ∨ p2)) ∨ p2))) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241638260017702438515111057001 : ((False → p5) ∧ ((((((p2 ∧ False) ∧ p2) ∨ p4) ∧ (p5 → ((p1 ∨ ((((True → p2) ∧ p3) → p3) ∨ p3)) → p2))) ∨ (p2 → p2)) ∨ p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_386207021366465647310737999462 : ((((((((p1 → (p1 → p4)) ∧ p5) ∧ True) → (((p4 → (False ∧ p5)) ∨ p1) ∨ (True → ((p3 → False) ∧ p5)))) ∨ (False ∨ True)) ∨ False) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54121162108074001375278098080 : (((True ∨ ((p1 ∧ False) ∨ (p1 → (p2 → (p3 ∨ p4))))) → ((((p4 → False) ∧ ((True → (p1 ∧ (p1 → p5))) → p5)) → True) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244615103865195703204262722766 : ((False ∧ p5) ∨ (((((p1 ∧ p2) ∧ (True → p3)) ∧ (p5 ∨ False)) ∧ (p1 ∨ (p1 ∧ (((((p3 ∧ p3) ∧ False) → p5) ∨ True) → p3)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207198146530573653570243322908 : ((((True ∧ (p3 ∨ False)) ∧ p3) ∨ p5) → ((p1 ∨ False) → (True ∧ ((((p1 ∧ ((False ∨ p5) ∧ p1)) → (True ∨ p3)) → False) ∨ (False ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h7 := h5.left
      let h8 := h5.right
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
        -- False on the left can always be used.
        apply False.elim h10
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h12 =>
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_555257361455195489709356103387 : (((p2 ∨ (True → (((False ∨ (((p2 ∨ (p4 ∧ (p2 ∧ p2))) ∨ p2) → p2)) → (False ∧ (p3 → ((p2 → (p1 → p1)) ∨ p1)))) ∨ True))) ∧ True) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199827967869879854714095969392 : ((((p5 → p1) ∧ (p5 ∧ p5)) ∧ (p4 → p4)) → (p5 → (((True → (False → ((((p2 → (True ∧ False)) ∨ p2) → p4) ∧ False))) → p4) ∨ p1))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h9 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h10 := h5 h9
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338595662100940620540451295845 : (p1 → (((p3 ∨ False) → p3) → (((p5 → (((True ∧ True) → False) ∨ False)) ∧ (p5 ∨ (True → (p2 ∨ p3)))) ∨ (p2 ∨ (True ∨ (p3 ∨ p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158513985485905280431412585721 : (((p1 ∨ p5) → (p1 ∨ (((True ∨ (True ∨ p3)) → (p1 ∨ ((p1 ∨ True) ∨ (p3 ∨ p1)))) ∨ False))) ∨ ((False ∧ (p2 ∨ p4)) ∨ (p5 ∧ p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329588488227487580927220878458 : (True → ((True → p3) ∨ (p4 ∨ (((((p4 ∨ (p5 → p3)) ∧ True) ∧ p3) ∧ (((p5 ∧ (p3 ∧ ((True ∨ p5) ∨ p1))) → p5) → p5)) ∨ True)))) := by
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
theorem thm_5_vars_783271996820699188429940583851 : (((p3 ∨ ((p2 ∨ (((p3 ∨ ((p5 ∧ (False ∧ (p3 ∨ ((p4 ∨ False) ∨ False)))) ∨ p5)) ∧ True) ∧ p1)) ∧ ((p4 ∨ p5) ∨ (p1 → True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_211266047457385655941389469683 : (((p3 ∧ p2) ∨ (False → p4)) ∧ (((((False → p1) ∨ (((p5 ∨ (((p1 ∨ p3) → p3) ∧ p4)) ∨ p3) ∧ p4)) → p1) → p2) ∨ (False → p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219638195921930210051147140300 : ((False → ((p2 ∧ p2) → p4)) → ((((False ∨ (True ∧ True)) → ((p2 → p3) ∧ False)) ∧ ((((True ∨ p3) → (p4 ∨ p3)) ∧ p4) ∨ False)) → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h8 : (False ∨ (True ∧ True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h9 := h3 h8
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196782999098420858948713090624 : ((((p4 ∨ False) ∧ (p4 ∧ (True → p4))) ∧ p3) ∨ (((False ∨ (p2 ∧ (p4 ∧ (((p1 ∧ (p2 ∨ p5)) ∧ p3) → p2)))) ∧ p1) → (p4 → p1))) := by
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
  cases h3
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702381727369071494635735667809 : ((((((False ∧ (p1 ∧ (p5 ∨ p2))) ∧ (p1 ∨ p2)) ∨ False) ∨ (((p3 ∧ p4) → p3) ∨ (((p5 ∨ ((p2 → p5) ∧ False)) ∨ p4) ∧ p4))) ∨ p4) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179207549699165718975460876202 : ((p4 ∧ (((p1 ∨ (False ∨ (((p4 ∨ p2) → p4) ∧ p1))) ∧ p3) ∨ False)) ∨ (p5 → (((p2 ∨ ((p3 → p5) → p5)) ∨ p1) ∧ (False → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172964474482442672793309959287 : ((p4 ∧ ((((False ∨ (p1 ∧ p5)) → ((True → p5) → p1)) ∧ p1) ∨ (p2 → p5))) ∨ (False ∨ ((False ∧ ((True → p1) ∨ (p5 ∧ True))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314660589131457919376107116868 : (p3 ∨ (((p1 → p5) → ((p4 ∨ (((p1 → p2) ∧ p5) ∨ p2)) ∧ ((p2 ∧ p4) → True))) ∨ ((p3 → ((p2 ∨ p3) ∧ (True → p3))) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350028742086538999261450685339 : (p4 → ((((((True ∨ (p4 ∧ ((p5 → (p5 ∨ (p5 ∨ p4))) → (p5 ∨ (p1 ∨ False))))) ∧ False) ∨ p5) → (p3 ∨ (p5 ∨ p5))) → p3) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246095387129393135626145794955 : ((p4 ∧ p1) ∨ (((((p3 ∨ p4) → (p2 ∨ True)) → (p2 ∨ p5)) ∨ True) → (((p5 ∨ p3) → (((p5 ∧ False) ∧ True) ∧ (False ∨ p4))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_49495151712125222517434205499 : (((((True ∨ p2) ∨ (((p5 ∨ (((p1 ∨ (False → p4)) → p1) → p3)) ∨ (p5 → (p2 ∧ p2))) ∧ True)) → p3) → (p4 → (p4 ∨ p2))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149394410869948768574948896104 : ((True ∧ (((p2 ∨ p3) ∨ (p1 → ((((p5 ∨ p3) → (p3 → p5)) ∧ ((True ∧ p4) → p5)) → p2))) ∧ p4)) ∨ (p4 ∨ (False → (p3 ∧ False)))) := by
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
theorem thm_5_vars_324992194625019396471486497997 : (p5 ∨ ((p4 → p2) ∨ ((p5 → (False ∨ (((((False ∨ True) → True) → p1) ∧ p1) → ((False ∨ True) ∧ (p2 ∨ ((True ∧ True) ∨ p4)))))) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
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
theorem thm_5_vars_60242865723401179338980810112 : (((True → p5) → (False ∨ (((p2 → False) → ((p4 ∧ ((p1 ∧ p3) → (p5 ∧ ((p5 ∧ (p2 ∧ p3)) ∧ p4)))) ∧ p3)) ∧ (p1 ∨ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323723150844387676412732709026 : (p5 ∨ (((p1 → False) ∧ (((p3 ∧ p2) ∨ True) ∧ (((p3 → p1) ∨ (False → p4)) → (False ∧ (p5 ∨ True))))) → (p5 → ((p2 → p5) → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h11 : ((p3 → p1) ∨ (False → p4)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- False on the left can always be used.
      apply False.elim h12
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h13 := h7 h11
    -- We need to get the left conjuct of h13 based on <expert-advice>.
    let h14 := h13.left
    -- False on the left can always be used.
    apply False.elim h14
  case inr h15 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h16 : ((p3 → p1) ∨ (False → p4)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h17
      -- False on the left can always be used.
      apply False.elim h17
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h18 := h7 h16
    -- We need to get the left conjuct of h18 based on <expert-advice>.
    let h19 := h18.left
    -- False on the left can always be used.
    apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190941751319359868305644761343 : ((((p3 ∨ p3) ∨ (p4 → p1)) ∧ (p3 ∧ (p2 ∧ False))) ∨ ((True ∨ (False ∧ False)) → (((False ∧ (p2 ∨ (p2 ∧ (p5 ∧ p4)))) → True) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245328032301059628047377004867 : ((p2 ∧ p2) ∨ (p3 ∨ (p5 ∨ ((((((p1 ∨ p3) ∨ True) ∨ p4) ∨ p1) ∨ (p2 → ((p4 ∨ (p2 ∧ p3)) → p4))) ∨ (p1 → (p1 → True)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135147177212467809554949617177 : (((p5 ∨ ((p5 ∧ p3) ∧ (p5 ∨ (True → ((p3 ∧ p4) → (False → (p3 ∨ (p5 ∨ (p3 ∨ p1))))))))) ∨ (p2 → p1)) ∨ (True ∨ (p3 → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_586241097886374232212537936862 : ((((((p3 → ((True → (((False ∧ True) ∨ p4) ∨ False)) ∧ p4)) ∧ (p4 ∧ ((p1 ∧ p5) ∨ (p4 ∨ (p4 ∧ (p4 ∧ p2)))))) ∧ p2) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694559853465038194884680590923 : ((((p2 ∧ ((((p3 → (p1 ∧ p1)) ∨ True) → p5) ∧ ((p2 → p4) ∧ p1))) ∨ (((p1 ∨ p3) ∧ (p2 ∧ True)) ∧ ((p1 ∨ p2) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244818835369832517159732645482 : ((p1 ∧ p1) ∨ (((True ∨ (((p5 → (True ∨ False)) → (p4 ∨ p2)) → p4)) → False) → ((p4 ∨ p1) ∧ (p5 ∨ (p5 ∧ ((p2 → p4) ∨ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ (((p5 → (True ∨ False)) → (p4 ∨ p2)) → p4)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : (True ∨ (((p5 → (True ∨ False)) → (p4 ∨ p2)) → p4)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60613728885548906239225967340 : ((True ∧ (((p5 ∨ (p4 ∨ (p3 → (True ∧ ((p2 ∨ True) ∨ ((False ∧ p1) → p2)))))) ∧ (((False → p5) ∧ True) ∧ p1)) ∨ (p2 ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319276972910085495252331360016 : (p4 ∨ ((((p5 → (p3 ∨ (True → False))) ∧ False) ∨ ((p5 ∧ p5) ∨ (False → (p3 ∨ p4)))) ∨ (((((p2 ∧ p2) → p2) ∧ p4) ∨ p5) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_347425016829275844634374655453 : (p3 → ((p4 ∨ (p4 ∧ (p2 → (p4 → (p1 → p3))))) → (((p2 → (p3 ∧ p1)) → p1) ∨ ((p5 ∨ p3) ∨ ((p2 ∨ (p5 → p2)) ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_735178624561626095344653380487 : ((((p3 ∨ p3) ∧ ((p4 ∧ True) ∧ (p2 → ((p5 ∧ (p4 → (p3 ∧ ((((p2 ∨ False) ∨ p3) ∧ p5) ∧ (p2 → (p3 ∨ True)))))) ∧ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_189045510455296470617683981828 : ((((p5 ∧ p2) ∧ p3) → (((p2 ∨ False) → p2) ∨ p5)) ∧ (((p5 ∨ ((p5 → (p3 ∧ p4)) ∨ (False ∧ (False ∧ p2)))) ∧ (p2 → False)) ∨ True)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_90090454471683589106930980724 : ((((p2 ∨ False) → p2) → ((((p2 ∨ p4) ∨ p1) ∨ (p4 → p2)) ∧ (False ∧ ((p1 → ((p2 → p1) ∧ ((p2 ∧ p4) ∧ p1))) → p1)))) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p2 ∨ False) → p2) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- False on the left can always be used.
      apply False.elim h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117116785381915544024254600707 : (((p3 → p3) → (((p1 ∨ (False → False)) ∧ ((p4 ∧ True) → (p2 ∧ (p2 → ((True → ((p5 ∨ p3) ∧ p2)) ∧ p2))))) ∨ p2)) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185740475500400280006182295817 : ((p3 → ((p3 ∨ ((p5 ∧ False) → p3)) → ((p2 ∨ p4) → p4))) ∨ (((p3 → (p5 → p5)) → (True ∨ False)) ∨ ((p4 → True) ∨ (p2 ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41154104710028459840218083483 : (((((True → p2) → ((True ∧ False) ∨ ((p4 ∨ (p2 ∧ p4)) → (((p4 ∧ (p5 → p1)) → p5) ∨ p5)))) ∨ (True ∨ (False ∧ p5))) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216024397726181891131380181317 : ((p5 ∨ ((p4 ∧ p4) ∨ p3)) ∨ (((p2 ∨ p3) ∨ (p2 → True)) ∨ (((((p1 ∨ (((p5 ∨ False) ∧ p5) ∨ False)) → False) ∨ p1) ∨ p4) ∧ True))) := by
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
theorem thm_5_vars_730702725014781653610957516896 : ((((p3 ∧ (p5 ∨ p2)) → ((p1 ∨ (p5 ∧ (((False → p5) ∧ (p5 ∧ ((p1 ∧ ((True ∨ p4) ∨ p1)) → p2))) ∧ (p5 → p3)))) ∨ True)) ∨ False) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_578120875873760811426460740387 : (((p3 → (((p4 ∨ (p1 ∨ p2)) ∨ p5) → ((p4 ∧ p2) ∨ (p3 ∨ (p5 → (False ∧ (True ∨ (p3 → (p4 → ((p1 → p5) ∨ False)))))))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h1
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_732297408385112684555278841262 : ((((False ∧ False) ∧ ((((((False ∧ p5) → p2) ∧ (p2 ∧ (False → p1))) → p3) ∨ (p1 ∧ p4)) ∨ ((p4 ∨ True) ∨ ((p1 ∨ False) ∧ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_762252058250045729447633893110 : (((p3 ∧ ((((p4 → (True ∧ p3)) ∧ p5) → (p4 → (((p4 ∨ (p3 → p4)) ∨ p5) ∨ (p4 ∨ (p2 → (p5 ∧ p4)))))) → (p4 → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231267851620659292286296060402 : (((p4 ∨ p5) ∨ p5) → (((p4 → ((False → ((p4 ∨ p1) ∨ False)) ∨ (p3 ∨ (False → ((p4 → p1) → p1))))) → (p2 ∨ (True → False))) ∨ True)) := by
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
theorem thm_5_vars_200074846646886694350222716889 : ((((p1 → p4) ∧ p2) ∧ (p4 ∨ (p5 → False))) → (p4 → ((p4 → (((p4 ∨ p4) ∨ (p2 ∧ (True ∨ (p4 ∧ False)))) ∧ (p4 → False))) ∨ p2))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321494465588077840310956674171 : (p4 ∨ (p1 → ((((p4 → (False ∨ (p2 ∧ (p1 ∧ ((p4 ∧ p5) → p1))))) → p5) → (p3 ∨ p3)) ∨ ((((p1 → False) → p4) ∧ p4) → p4)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610367750149056415192232247622 : (((((((((p4 ∨ True) → (((p1 → (p1 ∧ p2)) → (p3 → ((p3 ∨ p3) → False))) ∧ (p4 ∧ True))) ∧ p2) → p3) → p5) → p3) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_659676307480092181861135783936 : (((((((p2 → p1) ∧ p3) ∨ (p4 → (p3 → ((((p5 → ((p2 ∨ p5) ∧ False)) ∧ False) ∧ p4) → (p2 ∨ p3))))) ∧ p5) → (p1 → p1)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201973862863068021589864893760 : (((False → ((True → True) → False)) ∨ p5) ∧ (((False ∨ True) ∧ (p5 ∨ p4)) → ((((p1 ∧ (p2 → True)) → False) ∧ (p5 ∧ (p4 ∨ p5))) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
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
theorem thm_5_vars_191260443317811096215713989610 : (((p4 ∧ p5) ∧ (((p5 → p4) ∧ p4) → (p5 ∧ False))) ∨ (p3 → (p3 ∨ (((p2 → (p3 ∨ (p3 → (p4 ∧ p3)))) ∨ (p2 ∨ True)) ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166133907545797773188571151166 : ((True ∧ ((p3 ∧ p2) ∧ ((((p5 ∨ (p5 ∨ p4)) ∧ p2) → ((True ∧ p1) ∧ False)) ∨ p3))) ∨ (p2 ∨ ((((p4 ∧ p5) ∧ p1) ∧ True) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356384052893355252826365190303 : (p5 → ((((True → True) → ((p3 ∧ p2) ∧ p4)) ∧ ((p1 ∨ False) → (p2 → p2))) → (((p2 → (p1 ∨ (False ∨ False))) ∨ (False ∧ p5)) → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h2.left
    let h6 := h2.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : (True → True) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h9 := h5 h7
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149073181674504564728725218591 : ((((p1 → p3) ∨ p3) → (((((p3 ∨ (p2 ∨ p3)) → p3) ∨ p1) ∧ (True ∧ ((False ∧ p3) ∧ False))) ∧ p5)) ∨ ((p2 → (p3 ∧ p3)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



