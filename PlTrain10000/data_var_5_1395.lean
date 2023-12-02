variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324710910477741772732492712173 : (p5 ∨ (((p1 ∧ p2) ∨ p2) → ((((p5 ∧ True) ∧ ((p3 → (p1 ∨ ((False → True) → ((False ∧ (p3 ∧ p3)) ∨ True)))) ∨ False)) ∨ p2) ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
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
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_762451029797069879334813002279 : (((p3 ∧ ((((False ∧ ((False ∨ p5) ∧ False)) ∧ ((p4 ∧ ((True ∨ p4) → False)) ∧ (p2 ∧ p2))) ∨ p1) ∨ (p1 ∨ (p5 ∨ (p5 → p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172135443902213833108746946361 : ((((p4 ∧ p2) ∨ (((p3 ∨ False) ∧ False) ∧ (p3 ∨ p2))) ∧ (p1 → (p4 ∨ p2))) ∨ ((True → p5) → (p3 → ((True → (p5 ∧ p3)) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- One of the premise coincides with the conclusion.
  exact h5
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_129070946267591236497885181935 : (((((((False ∧ p1) ∧ (((p1 → False) → True) ∨ (False → (p4 → p2)))) ∨ (False ∧ p2)) ∨ (p5 ∧ p4)) ∨ p4) ∨ True) ∧ ((p5 ∧ p4) → True)) := by
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
theorem thm_5_vars_722469262928207066092441472467 : (((((False ∨ p4) ∧ p1) ∧ (((((p2 → (p5 ∧ p5)) → False) ∨ True) ∧ ((p4 ∨ ((False → (p4 ∨ (p3 → p3))) → p3)) ∨ p1)) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50817533676552327858667314520 : (((p4 → (True ∨ ((False → p2) ∧ (p5 → ((p4 → ((p4 ∧ p1) ∨ ((p2 → False) → p5))) → p5))))) → (((p2 ∨ p4) → p5) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46952236877736449479400779060 : ((((p4 → ((((p2 ∨ p1) → (((((False → p3) → p1) → (True ∧ p3)) ∧ True) ∧ p5)) ∨ (p5 → p2)) → False)) ∨ False) ∨ (True ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51228100898812902961481381228 : (((((p1 ∧ (p5 ∨ False)) ∧ p5) ∨ ((False ∨ p1) ∧ ((((True → False) ∨ p4) ∧ p4) ∧ p4))) ∨ (False → (False ∨ ((False → True) ∧ p4)))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_34973659758958719509345129418 : ((p1 → (((p4 ∧ (((p3 → (p3 ∧ p5)) ∧ (((((p5 → p1) ∨ True) ∨ True) ∨ p3) → False)) → (p4 → p1))) → (p4 ∧ p5)) ∨ True)) ∧ True) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328780186253508351906797343664 : (True → ((((((p5 → p4) → False) ∧ (True ∧ p3)) ∨ p3) ∧ p4) ∨ (((True ∨ False) ∨ True) ∧ (((((True → p2) ∧ p1) → p4) ∨ p2) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693504970305465701165888317989 : ((((((((p5 → (p5 ∨ (p4 → p3))) ∨ p2) ∨ False) ∧ (False → p1)) ∧ False) ∨ (p2 → (((p4 ∧ p4) ∧ ((True ∨ p4) → p5)) ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165835484825825383488324757780 : ((((True ∨ p4) ∧ p5) ∨ (p3 ∨ (p1 ∧ ((((p2 ∨ (p5 ∨ p1)) ∧ p2) ∨ p5) → p3)))) ∨ (True ∨ (((p2 ∨ p1) ∨ False) ∧ (False ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43426928104762797207108045368 : ((((((p2 → False) ∧ ((False ∨ p4) → True)) → (True ∨ (p5 ∨ (p2 ∧ (p2 → ((p1 → (p2 ∨ (p5 → False))) → p1)))))) ∨ p4) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54287693720755845728111642013 : ((((p2 → (False → p1)) → ((p4 ∧ p5) ∨ p1)) ∧ ((((p5 → p2) ∧ ((p3 ∧ p4) ∧ p5)) ∨ (p4 ∨ p5)) ∧ (False → (p5 ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134497581182278307499477484253 : (((((((p4 → True) ∧ (((False ∨ p3) ∧ (p5 → p4)) ∨ False)) ∧ p5) ∧ (((False ∨ p2) ∧ p5) ∧ p5)) ∨ p1) → False) ∨ (True ∨ (p5 ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157047278564951317197826908575 : (((p1 ∧ ((p5 → (p1 ∨ (True ∨ ((p5 ∧ ((p5 ∧ p2) ∧ p4)) ∨ (p3 ∨ True))))) → p4)) ∨ True) ∨ (p5 → ((False ∧ p4) ∧ (p2 ∨ p5)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66752023139579997177371771463 : ((True → (p1 ∧ ((p5 ∧ ((((p5 ∨ False) ∧ True) ∨ (p2 ∨ p4)) ∧ (((p2 ∧ p2) ∧ True) → (False → p4)))) → (True ∧ (p4 ∧ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52204516331268622727781586281 : ((((p5 ∧ p2) ∧ (((((True ∧ (p5 ∧ p1)) → p3) ∨ p3) ∨ (p1 ∧ p3)) ∧ p3)) → (False ∧ (p4 → (((p1 ∨ p1) ∨ p3) ∨ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175382336376895489251907347844 : ((True → (((p5 ∧ (p4 ∧ p4)) ∧ True) ∨ (True → (((p1 ∧ p5) ∨ p5) ∨ p5)))) → ((p4 ∨ (p1 ∨ ((True → True) → (p4 ∧ False)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174483795711966912283773776031 : (((p4 ∧ (p2 ∧ (p2 ∨ (p5 ∧ True)))) ∧ (p2 ∨ (((p5 ∨ True) ∨ False) → False))) → (((((p5 → p2) ∧ p3) ∧ p3) ∨ p3) ∨ (p2 → True))) := by
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
  cases h7
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h9 =>
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
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h17
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h19
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318857068175798277040897131434 : (p4 ∨ (((((p3 → (p3 ∧ (((p5 ∧ False) → (True → ((False ∧ p4) ∨ p4))) ∧ (p5 ∧ p5)))) ∨ True) ∨ False) → False) ∨ (p5 → (False → p3)))) := by
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
theorem thm_5_vars_78875293611452097359969005380 : ((((p2 ∨ p3) ∧ ((((False ∧ True) ∧ ((p2 ∧ ((p1 ∨ p4) ∧ (p3 ∨ p4))) ∧ True)) → p3) → (True ∧ (p1 ∧ p1)))) ∧ (p5 → p3)) → p1) := by
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
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : (((False ∧ True) ∧ ((p2 ∧ ((p1 ∨ p4) ∧ (p3 ∨ p4))) ∧ True)) → p3) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h9.left
      let h12 := h9.right
      -- False on the left can always be used.
      apply False.elim h11
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h13 := h5 h7
    -- We need to get the right conjuct of h13 based on <expert-advice>.
    let h14 := h13.right
    -- We need to get the left conjuct of h14 based on <expert-advice>.
    let h15 := h14.left
    -- One of the premise coincides with the conclusion.
    exact h15
  case inr h16 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h17 : (((False ∧ True) ∧ ((p2 ∧ ((p1 ∨ p4) ∧ (p3 ∨ p4))) ∧ True)) → p3) := by
      -- Implications on the right can always be decomposed.
      intro h18
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- Conjunctions on the left can always be decomposed.
      let h21 := h19.left
      let h22 := h19.right
      -- False on the left can always be used.
      apply False.elim h21
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h23 := h5 h17
    -- We need to get the right conjuct of h23 based on <expert-advice>.
    let h24 := h23.right
    -- We need to get the left conjuct of h24 based on <expert-advice>.
    let h25 := h24.left
    -- One of the premise coincides with the conclusion.
    exact h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53728251486450925469031029167 : (((p1 → (((True ∨ (p5 ∨ (True → False))) ∧ p3) ∨ p5)) ∧ (p4 → ((((p5 → p4) → (p2 ∧ ((p5 ∧ p4) ∧ p4))) ∧ p3) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315843422402092008297181259324 : (p3 ∨ ((False → p4) → (((((p2 ∧ (p1 ∧ p1)) ∨ (p5 ∨ p1)) → ((p1 ∨ ((p2 ∨ p3) → True)) ∨ (p3 → p4))) → p1) → (p3 ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (((p2 ∧ (p1 ∧ p1)) ∨ (p5 ∨ p1)) → ((p1 ∨ ((p2 ∨ p3) → True)) ∨ (p3 → p4))) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h12
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h13 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h13
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h14 := h2 h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_558962651766959310238630316929 : (((p4 ∨ (((True ∧ p1) ∨ (((False ∧ p3) ∨ (p2 → p1)) ∧ (True → (p4 → (((False ∨ p3) → (p1 ∨ (False ∧ p1))) ∧ True))))) ∨ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230896727074911987104975862189 : (((p2 ∧ p2) ∨ p5) → ((((((True ∨ p3) ∨ p4) ∨ (p1 ∧ p1)) → (True ∧ (p3 ∨ (p2 ∧ p2)))) ∨ ((True ∧ False) ∧ (False ∧ False))) ∨ True)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342027958844154052808706747431 : (p2 → (((((((p3 → (False ∨ (False ∨ p3))) → (p2 ∨ p1)) → p2) → p5) ∨ (p2 ∧ ((p3 ∧ p2) → p4))) ∧ p5) → (p4 ∨ (p2 ∨ p2)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64976572015114010834363889052 : ((p2 ∨ ((p2 ∨ (p4 ∨ (False ∧ p4))) ∧ ((p2 → True) ∨ (p1 ∨ (((p2 ∨ p4) → (p5 ∧ (p2 → ((p1 → p1) ∧ p4)))) ∧ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_651104322317334169873908899328 : ((((((p4 → (p5 → p4)) ∧ p5) ∨ ((((p1 → p3) → (p5 ∧ p1)) ∧ (p3 → (((p1 → p5) → p1) → p1))) ∨ p4)) ∧ (p2 → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246508821370014717542173150523 : ((p5 ∧ p1) ∨ ((False ∧ (True → ((p5 ∨ (((True → p4) ∧ (((True ∧ True) ∧ True) ∧ (False → False))) ∧ p2)) ∧ (p3 ∧ True)))) ∨ (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60102362570402084600217666970 : (((p3 ∨ p1) → (p1 ∨ (((p1 ∧ p2) ∧ (False ∨ (((p2 ∨ p5) ∧ (True → True)) → (((p4 → False) → p1) ∧ p2)))) ∧ (p1 ∧ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114969092152280676237531379270 : (((p4 → (((False ∧ True) ∧ p1) → (((False ∨ (False ∧ p2)) ∧ p2) ∧ p3))) → ((((False → p3) ∧ p5) ∧ p3) ∧ (p1 → p4))) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165701229251348352240410580751 : (((((p4 ∧ p3) ∨ p1) ∧ p3) ∧ (True ∧ (((p5 → (False ∨ (p1 → p2))) ∧ False) ∨ p5))) ∨ (p3 → (p4 ∨ (p4 ∨ (p5 → (p5 ∧ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115297679983807136306428185817 : ((((p1 ∨ (p5 ∨ (p2 ∨ ((p3 → p5) → p4)))) ∨ p2) → ((((p5 ∧ p1) ∨ p4) ∧ (((p3 ∧ p1) ∧ p5) ∨ p3)) ∧ p2)) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234821485549253062833304164930 : ((p5 → (False ∨ p4)) → (True → ((((((p5 ∨ p4) ∨ p1) → False) ∨ ((False → (p2 ∧ False)) ∧ False)) ∨ (p1 ∨ (p2 ∨ True))) ∨ (p3 ∧ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
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
theorem thm_5_vars_256987799604912442101251866007 : ((p1 ∨ p5) → (p3 ∨ (((p1 ∧ p4) ∧ (((p1 ∧ p3) ∨ ((p5 ∨ p2) → p4)) → False)) → (((p1 ∧ (p4 ∨ (p5 → p3))) ∨ p2) ∧ False)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h6
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h3.left
    let h9 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h12 : ((p1 ∧ p3) ∨ ((p5 ∨ p2) → p4)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h15 =>
        -- One of the premise coincides with the conclusion.
        exact h11
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h16 := h9 h12
    -- False on the left can always be used.
    apply False.elim h16
  case inr h17 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h18
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- Conjunctions on the left can always be decomposed.
    let h21 := h19.left
    let h22 := h19.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h21
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h22
    -- Conjunctions on the left can always be decomposed.
    let h23 := h18.left
    let h24 := h18.right
    -- Conjunctions on the left can always be decomposed.
    let h25 := h23.left
    let h26 := h23.right
    -- We want to use the implication h24 based on <expert-advice>. So we show its premise.
    have h27 : ((p1 ∧ p3) ∨ ((p5 ∨ p2) → p4)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h28
      -- Disjunctions on the left can always be decomposed.
      cases h28
      case inl h29 =>
        -- One of the premise coincides with the conclusion.
        exact h26
      case inr h30 =>
        -- One of the premise coincides with the conclusion.
        exact h26
    -- We have shown the premise of h24, we can now drive its conclusion.
    let h31 := h24 h27
    -- False on the left can always be used.
    apply False.elim h31



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682951568612572756508267427899 : (((((p4 ∨ p3) ∨ (((False → (((p3 → p5) ∨ (p4 ∨ True)) ∨ (p5 ∨ p5))) ∨ p4) ∧ True)) ∧ ((p3 ∨ p2) ∨ (p1 ∨ (p1 ∨ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115189985407387074121873340053 : (((((p4 ∨ (p4 ∨ p3)) → True) → ((False ∨ False) ∧ False)) ∧ (((p5 ∧ False) → (((p4 ∨ p3) ∨ p5) ∨ (p1 ∨ False))) → False)) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_806773927185303103216466466211 : (((p4 → ((((((p3 ∧ ((p1 ∧ False) ∧ p5)) → (True → ((p4 → p3) ∧ (p3 ∧ (p5 ∧ p2))))) → p1) ∧ p4) ∨ False) ∨ (p1 → p4))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52665416241335029505797298889 : (((p5 ∧ (((((p5 → p3) → p2) ∧ (p2 ∨ p5)) ∧ p3) ∨ (p5 ∧ p3))) ∨ ((p3 ∧ p2) ∧ ((p2 ∧ (p3 ∧ (p5 ∨ False))) → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1529267100979639239698104583 : ((((False ∨ p2) ∨ p2) → (p5 ∨ (((p2 ∨ ((False → True) ∨ ((((p3 → True) ∧ False) ∨ True) ∨ p5))) → False) ∧ False))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147055396800741909689118890994 : ((((False ∨ (((p3 ∨ p2) → (False ∧ False)) → (p5 ∧ p1))) ∨ (((p4 ∧ (p2 ∧ p3)) ∨ p5) → p2)) ∧ False) ∨ (((True ∨ False) → True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133753790400617450438437945778 : ((((((p2 ∧ (p2 ∧ p5)) ∧ False) ∧ True) ∧ (p1 ∨ (((p2 ∨ p2) ∧ (False ∧ (p5 ∧ (p4 ∧ True)))) ∧ p2))) ∧ p3) ∨ (p3 → (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699289902123890529066734629559 : (((((((p2 → (True ∨ p1)) ∨ ((p2 ∨ p5) ∨ True)) ∨ False) ∧ p2) → ((p2 ∧ ((p3 ∧ (False ∨ True)) ∧ (p4 → p3))) ∨ (p1 ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42079696056244187043702834775 : ((((p2 → False) ∨ ((((p2 → ((False → p5) → (p2 ∨ p2))) ∧ p5) ∧ ((p5 ∨ (False ∨ (p4 ∧ p5))) ∧ True)) → (p3 → p2))) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185595239967065446399497654805 : ((p5 ∨ ((p3 ∧ p5) → (False ∧ ((p2 ∨ (p5 ∧ False)) → False)))) ∨ ((p4 → (p1 ∨ (p5 ∨ p3))) ∨ ((False → (p1 ∧ (p4 ∧ p5))) ∨ p3))) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_753367216856712883485254028338 : (((False ∧ ((((((True ∧ (True ∧ ((p1 → (p4 ∧ p5)) → True))) ∨ p5) ∨ False) → (p3 → (False ∧ False))) → False) ∧ (p4 ∨ (p1 ∨ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245057799758278904707621362578 : ((p1 ∧ p5) ∨ ((p5 ∨ ((True ∨ (p2 ∨ False)) ∨ (p5 ∧ (False ∧ (True → (p1 → ((p2 ∨ p3) ∧ True))))))) → (p1 ∨ (False → (p5 → p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h3
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
        -- Implications on the right can always be decomposed.
        intro h9
        -- False on the left can always be used.
        apply False.elim h8
      case inr h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h12
          -- Implications on the right can always be decomposed.
          intro h13
          -- False on the left can always be used.
          apply False.elim h12
        case inr h14 =>
          -- False on the left can always be used.
          apply False.elim h14
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- False on the left can always be used.
      apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174068761620936906484014557175 : (((((p1 → True) ∨ (((True ∨ False) → (p4 ∨ False)) → p3)) ∧ p1) ∧ (p5 → p4)) → (((p3 ∨ (False ∨ (False ∧ (p5 → False)))) ∨ True) ∨ p4)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140516630371428606863119223095 : (((p3 ∧ ((p4 ∨ (p3 ∨ p4)) → ((p3 → (p5 ∨ ((True ∧ p3) → False))) → p5))) ∧ (p5 ∧ (p2 → (True → p1)))) → ((True ∧ p1) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h3.left
  let h7 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42539028956782456481189030459 : (((p1 ∨ ((True ∨ (((True → (False ∨ ((p5 ∧ p5) ∨ (((p1 → p1) ∧ p4) ∨ p1)))) ∨ (p5 ∨ True)) ∨ p4)) → (p3 ∨ False))) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62718370391797532329206463524 : ((p4 ∧ ((p3 ∨ (((((p2 ∧ (((p1 → p5) ∧ True) → p2)) → ((((p2 → p1) ∧ p5) ∨ p1) ∧ True)) ∨ p2) ∨ False) ∧ p1)) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345623423372163947570735686280 : (p3 → ((True ∧ (p2 ∨ ((((p4 ∨ (p5 → False)) → ((p1 ∧ (p5 → p2)) ∨ (True ∨ (((p4 ∧ p4) ∨ p3) ∨ False)))) → p3) → p2))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115617887399489361555225450645 : (((False → (p4 ∧ ((p4 ∧ True) ∧ False))) ∧ ((((p4 ∨ p5) → p3) ∧ p4) ∨ (((False → ((p2 → False) → True)) → p3) ∧ p2))) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264195023251077882540265903625 : (True ∧ (((True ∨ ((p5 ∧ p5) → p2)) ∨ (p1 ∨ p5)) → ((p5 ∧ (((p4 ∧ True) ∧ (p3 ∧ p3)) ∨ (p1 ∧ (p5 → p3)))) → (p3 ∨ p4)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h7.left
    let h11 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h14 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h11
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h17 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h11
  case inr h18 =>
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h21 =>
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h22 =>
        -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
        have h23 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h3
        -- We have shown the premise of h20, we can now drive its conclusion.
        let h24 := h20 h23
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h24
      case inr h25 =>
        -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
        have h26 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h3
        -- We have shown the premise of h20, we can now drive its conclusion.
        let h27 := h20 h26
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h27
    case inr h28 =>
      -- Disjunctions on the left can always be decomposed.
      cases h28
      case inl h29 =>
        -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
        have h30 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h3
        -- We have shown the premise of h20, we can now drive its conclusion.
        let h31 := h20 h30
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h31
      case inr h32 =>
        -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
        have h33 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h32
        -- We have shown the premise of h20, we can now drive its conclusion.
        let h34 := h20 h33
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h34



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112975422368337662166134716035 : (((p1 ∧ (False ∨ (((p2 → False) ∨ p4) → ((((p4 ∨ p2) → (p2 → ((False → p2) ∧ (True ∧ True)))) ∨ p3) ∧ p2)))) → p3) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234581498795392001171742454757 : ((p3 → (False ∨ False)) → ((True ∧ ((((p5 → (p4 ∧ ((p2 → p5) → p4))) ∧ p1) ∨ (p1 ∨ True)) → ((False ∧ p4) ∨ (True ∨ p5)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_873292736338044019517163472885 : ((((p2 → ((False ∧ ((p3 ∧ p2) ∨ ((True ∧ p3) → (((p1 ∧ (p4 ∨ ((p1 ∧ p4) ∧ p3))) ∨ False) ∧ p2)))) ∨ (True ∨ True))) → False) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 → ((False ∧ ((p3 ∧ p2) ∨ ((True ∧ p3) → (((p1 ∧ (p4 ∨ ((p1 ∧ p4) ∧ p3))) ∨ False) ∧ p2)))) ∨ (True ∨ True))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_596003101898857253898390038673 : (((((((False → False) ∧ (p1 ∨ (p4 ∧ (p1 ∨ p4)))) ∧ p1) → (((p2 → (True ∨ p5)) → (p5 → (p3 ∧ (p1 ∧ False)))) → False)) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_631259813762544948252080738166 : (((((((((p4 → (p5 ∨ p4)) → True) ∨ p4) ∨ (((((p2 ∨ (p5 → True)) ∧ False) ∧ (p1 ∧ p5)) ∨ p5) → p5)) → False) → p2) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680417175896530836561817103567 : (((((((((True ∨ p1) ∨ (p3 → p1)) → (p4 → p2)) → p2) ∧ False) ∨ ((True → (p1 ∨ False)) → p1)) → (False ∧ ((True ∧ p3) ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161835025546494416597172534071 : ((True → ((((p5 ∧ ((p1 → False) ∨ ((p4 ∨ p2) ∨ (True ∧ False)))) ∧ False) ∧ p3) ∧ (p1 ∨ False))) → ((((p3 → p1) ∧ True) ∧ True) → p4)) := by
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h7
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158067244381908625269105873098 : ((((p5 → ((p2 → False) → False)) ∧ p2) → (((((p2 → (p5 ∧ p3)) → p4) ∧ p4) ∨ False) ∧ p3)) ∨ (((p2 ∨ p4) ∨ (p4 ∨ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_597473628664936714267251459932 : ((((((True ∧ p1) → (False ∨ p4)) ∨ (((True ∨ (((True ∧ p3) ∨ (p1 ∨ p4)) ∨ True)) ∧ p3) ∧ (((p2 → p1) ∧ False) ∨ p3))) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168682371054225557904333655232 : ((p5 ∧ ((p3 ∧ (p2 → p2)) ∨ (p1 ∨ (p5 ∨ (((True ∧ (True → True)) ∧ True) ∨ p1))))) → (((p1 ∨ p1) ∨ True) ∧ ((p5 ∧ True) ∨ p3))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
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
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Conjunctions on the left can always be decomposed.
          let h13 := h12.left
          let h14 := h12.right
          -- Conjunctions on the left can always be decomposed.
          let h15 := h13.left
          let h16 := h13.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h17 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h18 := h1.left
  let h19 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h19
  case inl h20 =>
    -- Conjunctions on the left can always be decomposed.
    let h21 := h20.left
    let h22 := h20.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h21
  case inr h23 =>
    -- Disjunctions on the left can always be decomposed.
    cases h23
    case inl h24 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h18
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h25 =>
      -- Disjunctions on the left can always be decomposed.
      cases h25
      case inl h26 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h26
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h27 =>
        -- Disjunctions on the left can always be decomposed.
        cases h27
        case inl h28 =>
          -- Conjunctions on the left can always be decomposed.
          let h29 := h28.left
          let h30 := h28.right
          -- Conjunctions on the left can always be decomposed.
          let h31 := h29.left
          let h32 := h29.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h18
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h33 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h18
          -- True on the right can always be proven directly.
          apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114768142575810495514796178545 : (((p4 → ((p1 ∧ (((True → p2) ∨ ((True ∨ p2) → p5)) → (p4 ∨ p5))) → p3)) → ((True ∧ (False ∨ p4)) ∨ (True → p4))) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358531598391751908683780587426 : (p5 → (p2 → ((((p3 ∨ ((((((False → p4) ∨ p1) ∨ (p3 ∧ p1)) ∧ p3) → False) ∨ (p3 ∨ False))) ∨ p3) ∧ (False ∨ p1)) ∨ (p4 ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137016005828266400839383202331 : (((p2 ∨ p3) → (((False ∨ ((p5 → (p3 → (((((p4 ∨ p1) ∧ p1) → p2) ∧ p5) ∨ p4))) ∧ True)) ∨ True) ∨ False)) ∨ (p4 → (p5 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251157501633353325573720517355 : ((p2 → False) ∨ (p3 ∨ ((p4 ∨ (((((p2 ∧ p4) ∧ False) → p3) ∧ (False ∨ False)) ∨ (False → ((((False → p1) ∨ p4) ∨ p4) → p1)))) ∨ p1))) := by
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
      -- False on the left can always be used.
      apply False.elim h1
    case inr h5 =>
      -- False on the left can always be used.
      apply False.elim h1
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53729963381231949136425780764 : (((p1 → ((p1 → p5) → ((p5 ∨ True) ∨ (p2 → p4)))) ∧ ((((p1 ∧ p2) ∨ (p5 → False)) ∨ ((p3 → (p5 ∧ False)) ∨ p3)) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_737391373064895789720164257937 : ((((p4 → p3) ∧ (p2 ∨ (True ∧ (((((((p2 → False) → (p2 ∧ p4)) ∨ p5) ∨ True) ∨ p5) ∨ ((p4 ∧ False) → (True ∧ p3))) ∧ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171943799127984120192205617846 : ((((p5 → (True ∧ (p4 → (p5 → (False → True))))) ∧ (p1 ∨ p2)) ∧ (False ∧ p2)) ∨ ((p5 ∨ True) ∨ ((p2 ∨ p4) ∧ (p1 → (p2 → p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206514219533605291964645810324 : ((p5 ∨ (p4 ∨ (p3 ∧ (p1 ∧ p2)))) ∨ ((p3 → (p3 → ((p5 ∧ (p4 ∨ p3)) ∧ (((True ∨ ((p1 ∧ p1) ∨ p5)) ∨ False) → p4)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51855645683508579225236223958 : ((((p1 → (((p5 ∧ (p2 ∨ (p3 → ((p4 ∧ p2) ∨ p4)))) ∨ p1) ∨ p1)) ∧ p3) ∨ (((True → p1) ∧ p5) → ((p1 → p2) → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53196885400860500608379626340 : (((((False → (p1 ∧ (p3 ∨ p5))) → (p3 ∨ False)) ∨ (p5 ∧ p2)) ∨ ((True ∨ (((False ∧ p5) ∨ (p2 ∨ p2)) → p3)) ∨ (p3 ∧ p4))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177650736511525524383474590413 : ((((((False ∨ (p4 ∧ ((True ∨ p3) ∧ p5))) → False) → p4) ∨ p2) ∧ True) ∨ ((p3 ∨ p2) ∨ (True ∧ (True → (False ∨ ((p1 ∧ True) → True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_744673206381600492622982098736 : ((((p3 ∧ True) → (p2 ∨ ((p4 ∨ ((True → (p5 ∨ (p4 → p5))) ∨ p2)) ∨ ((False ∧ ((p4 ∧ (p2 → p1)) ∧ p4)) ∨ (p4 → p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116212368802538115975001155116 : ((((p2 ∧ True) ∨ p4) ∨ ((p1 → (p1 ∧ ((False ∧ False) ∧ (p3 ∨ ((False ∧ p2) ∨ True))))) ∨ (((p3 → True) ∨ p2) ∨ p1))) ∨ (p2 ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49887045167991131413100909282 : ((((((p4 ∨ (((p4 ∨ False) ∧ p1) ∨ p2)) ∨ (False → False)) → ((False → (p1 ∧ p1)) → False)) ∨ p3) ∧ ((True → (p4 ∨ False)) → True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117459175739153596688416209176 : ((p1 ∧ ((p5 ∧ True) ∨ (((((p1 ∨ (p3 ∨ ((p2 ∨ p1) ∧ p1))) ∨ (False ∨ p4)) → p2) ∧ p5) ∧ ((p5 ∧ p3) → True)))) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38256708428882547991784419260 : (((((p1 → True) → ((((True → (False ∨ (p1 ∨ (p5 → p2)))) ∨ p2) ∧ True) ∨ (p5 ∨ p3))) ∧ (p3 ∧ (p3 ∧ (p1 → True)))) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114478730340379611623319431170 : ((((p5 ∨ (((p1 ∨ p5) ∧ ((False ∧ (p5 ∧ p5)) ∧ (p2 → p1))) → p4)) ∧ (p1 ∧ p3)) → ((p4 ∨ p4) → (p5 ∧ p5))) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59949974524673843334402896260 : (((True ∨ p2) → (False ∧ (p3 ∧ ((p2 ∨ (p1 ∧ p4)) ∧ ((p2 ∨ p1) → ((p3 ∨ ((p4 ∧ True) ∧ p1)) ∧ (p3 ∧ (False → True)))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117237851844808211531819782753 : ((True ∧ (p5 ∧ (((p1 ∨ ((p1 ∨ p4) ∨ (((p2 → p5) ∨ p2) → False))) ∧ ((p1 ∧ (p3 ∨ True)) → (True ∨ p5))) ∧ p4))) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_917575330745788002246048409417 : (((((((p1 ∧ p5) ∧ ((True ∧ p2) ∧ p4)) ∨ (p3 ∧ p5)) ∨ (p4 ∨ (True ∨ p1))) → ((True → p5) ∨ (False ∧ ((p1 ∨ True) ∧ p5)))) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p1 ∧ p5) ∧ ((True ∧ p2) ∧ p4)) ∨ (p3 ∧ p5)) ∨ (p4 ∨ (True ∨ p1))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147362624794489223349133708286 : (((((p1 ∨ False) → ((p2 ∧ p4) ∨ ((True ∨ p3) ∨ (p2 ∧ (p4 → False))))) → ((False ∧ False) ∧ False)) ∨ p4) ∨ ((p2 ∨ p4) → (True ∨ p5))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_444361504728870768233561150154 : ((((p3 ∧ (((p1 → p4) ∨ ((((p5 ∧ True) ∧ True) ∨ (p3 ∨ (p1 ∨ True))) → p1)) ∨ (p2 ∧ (p3 ∧ p3)))) ∨ ((True ∨ p4) ∨ p1)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219247771034896802568373603698 : ((p1 ∨ ((False → p3) → p1)) → (((False ∧ p5) ∧ ((p4 ∨ ((False → ((p3 → False) ∨ (p2 ∧ p3))) ∧ p3)) → p5)) ∨ ((p5 → True) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68001935042311954226396662246 : ((p2 → ((p4 → p1) ∨ ((p3 ∧ (((((p3 ∨ (True ∨ p3)) ∧ False) ∧ False) → (((False ∨ p4) → (p4 → p2)) → p2)) → p3)) ∨ True))) ∨ p3) := by
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
theorem thm_5_vars_336431505873044865445901378787 : (p1 → ((p2 ∨ (((((p2 → p3) ∨ (True → False)) → p2) ∧ (False ∨ p1)) ∧ ((p5 ∨ (((p4 → p2) ∨ (False → p5)) ∨ p4)) → p2))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305862231321670084156868698709 : (p1 ∨ (((p3 ∧ ((True ∧ p4) ∧ p4)) ∧ p3) ∨ (p1 → (((((((True → (p3 ∨ True)) ∧ p3) → p1) → (p5 → p1)) ∨ p5) ∨ p5) → True)))) := by
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
theorem thm_5_vars_49424956329267830041770339323 : ((((((p2 ∨ (p4 ∧ p2)) → (p2 ∧ ((((p5 ∨ (True ∨ False)) → True) ∧ p1) ∨ (p3 ∧ p3)))) ∧ p2) ∨ p3) → ((p3 ∨ False) ∨ p1)) ∨ p1) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : (p2 ∨ (p4 ∧ p2)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h5
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h13
  case inr h14 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40025817385540884790476043460 : (((((((p2 → False) → (p4 ∨ (p4 ∨ ((((p2 → p4) ∨ (p3 → False)) ∨ False) ∨ ((False → p4) ∧ p1))))) ∨ False) ∧ p4) ∧ False) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116362536504230763419482877032 : ((((True ∧ p4) → False) → ((p2 ∨ p4) ∧ (p3 → (p2 ∨ ((True → (p1 ∨ (False → ((p2 ∧ p4) ∧ False)))) ∧ (p4 ∧ True)))))) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60551912828883355666397931145 : ((True ∧ ((False ∨ ((((p5 ∨ ((p1 → (False ∧ True)) ∨ (p5 → p5))) → False) ∨ (p5 ∨ (((p5 ∨ p1) ∨ p3) ∨ True))) ∧ False)) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67428587191339912337058964229 : ((p1 → ((((p3 ∨ True) → p5) ∨ ((((p1 → False) ∨ False) → ((p3 ∧ (p1 → True)) ∨ p3)) ∨ ((p4 ∧ p1) ∨ True))) → (False ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_432253150092800771685020709261 : ((((p5 ∨ ((p2 ∧ True) ∨ ((False ∧ p4) ∧ (((((p3 ∨ p5) → (p2 ∧ False)) ∧ (True ∨ True)) ∨ (False ∧ True)) ∧ True)))) ∨ (p3 ∨ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609115969556806103598679046938 : (((((((True ∨ (p1 → (p4 ∧ p3))) ∨ False) → (p4 → ((p4 → ((p5 ∨ p2) ∧ True)) ∨ ((p2 ∧ False) → (False → p1))))) ∨ p4) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310340054355254191766373065513 : (p2 ∨ ((p3 ∧ ((p4 → p4) ∧ ((p3 → p3) → (p5 ∧ False)))) → (((p1 ∧ ((True ∨ False) ∨ p1)) ∧ (False ∨ (p3 ∧ (True ∧ p2)))) → False))) := by
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
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h9 =>
        -- False on the left can always be used.
        apply False.elim h9
      case inr h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- Conjunctions on the left can always be decomposed.
        let h15 := h1.left
        let h16 := h1.right
        -- Conjunctions on the left can always be decomposed.
        let h17 := h16.left
        let h18 := h16.right
        -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
        have h19 : (p3 → p3) := by
          -- Implications on the right can always be decomposed.
          intro h20
          -- One of the premise coincides with the conclusion.
          exact h20
        -- We have shown the premise of h18, we can now drive its conclusion.
        let h21 := h18 h19
        -- We need to get the right conjuct of h21 based on <expert-advice>.
        let h22 := h21.right
        -- False on the left can always be used.
        apply False.elim h22
    case inr h23 =>
      -- False on the left can always be used.
      apply False.elim h23
  case inr h24 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h25 =>
      -- False on the left can always be used.
      apply False.elim h25
    case inr h26 =>
      -- Conjunctions on the left can always be decomposed.
      let h27 := h26.left
      let h28 := h26.right
      -- Conjunctions on the left can always be decomposed.
      let h29 := h28.left
      let h30 := h28.right
      -- Conjunctions on the left can always be decomposed.
      let h31 := h1.left
      let h32 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h33 := h32.left
      let h34 := h32.right
      -- We want to use the implication h34 based on <expert-advice>. So we show its premise.
      have h35 : (p3 → p3) := by
        -- Implications on the right can always be decomposed.
        intro h36
        -- One of the premise coincides with the conclusion.
        exact h36
      -- We have shown the premise of h34, we can now drive its conclusion.
      let h37 := h34 h35
      -- We need to get the right conjuct of h37 based on <expert-advice>.
      let h38 := h37.right
      -- False on the left can always be used.
      apply False.elim h38



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42648593968758228587924185204 : (((p4 ∨ ((((p5 → (((p3 ∨ p1) ∨ (p5 ∨ p4)) → True)) ∨ p3) ∧ ((p3 ∧ (p3 ∨ (p1 ∧ (p5 ∨ p3)))) ∨ p1)) ∨ True)) ∨ p5) ∨ p1) := by
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



