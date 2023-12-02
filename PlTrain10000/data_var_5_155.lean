variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330720996182427732529712765143 : (True → (p1 → (((False ∧ (p3 ∨ (p4 ∨ ((p2 ∨ p4) → (((False ∧ False) ∧ True) ∧ (((True ∧ p4) → False) → p5)))))) ∧ (False → p3)) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342336077910022154801490587401 : (p2 → ((p5 ∧ ((((p4 ∨ p1) ∧ (((p3 → False) → p4) ∧ (p3 → p2))) ∨ (p2 → p5)) → False)) → ((p1 ∨ p5) ∧ (p1 ∧ (True ∧ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : (((p4 ∨ p1) ∧ (((p3 → False) → p4) ∧ (p3 → p2))) ∨ (p2 → p5)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h9 := h6 h7
  -- False on the left can always be used.
  apply False.elim h9
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206092504253595616315104741000 : ((p3 ∧ (p3 ∨ ((p5 ∧ p2) ∨ False))) ∨ ((((p5 ∨ ((((True ∧ (p2 ∧ p1)) ∧ (True → p5)) → p3) → p2)) → p1) ∨ (False → p1)) ∨ p5)) := by
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
theorem thm_5_vars_114526901318341411802680466323 : (((False ∨ ((p4 ∧ p4) → ((False → (((p1 ∧ p1) → True) → (p1 → (True ∧ True)))) ∨ p3))) → (p4 ∨ ((p4 → p5) ∧ True))) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160097310802396814141055921939 : (((p5 ∨ (False ∧ (((((((p2 ∧ p5) → False) ∨ (p4 → True)) → False) → p1) ∨ p2) ∨ p5))) → False) → (True → (p1 → (True → (True ∧ p1))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_864538948054445617001103734462 : ((((((((p3 ∧ p5) ∧ p5) ∧ p1) ∧ (p4 ∨ p2)) ∨ (p4 ∨ (False ∨ (((p1 ∧ (((False → False) → True) ∨ p2)) ∧ p4) → p4)))) → False) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((p3 ∧ p5) ∧ p5) ∧ p1) ∧ (p4 ∨ p2)) ∨ (p4 ∨ (False ∨ (((p1 ∧ (((False → False) → True) ∨ p2)) ∧ p4) → p4)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h2
  -- False on the left can always be used.
  apply False.elim h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55145768934137431352576080573 : (((((p5 ∨ (False ∧ p4)) ∨ False) ∨ p3) ∨ (p5 ∨ (p4 → ((((p1 → p3) → (p2 ∨ (p3 ∧ (p1 ∨ p1)))) ∧ (p2 → p3)) ∨ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198647771280681621744978748105 : ((p3 ∨ ((p1 → p4) ∨ ((p2 ∧ p4) ∨ p2))) ∨ ((p2 ∨ (((p1 ∧ p4) ∧ ((False ∧ (p1 ∨ p5)) → (p3 ∧ (p1 ∨ p5)))) → p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51254714388799327349426966928 : ((((p3 → p4) ∧ ((p5 ∧ True) → (p5 ∧ (((True ∧ p4) → p3) ∨ ((p4 ∨ True) → p3))))) ∨ ((((p5 → p3) → p5) ∧ p4) → p4)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114366257418387757228595882232 : (((((((p3 ∨ (True ∧ True)) → p5) → ((((False ∧ p5) ∧ p4) ∨ p2) ∨ p1)) ∨ True) ∨ True) ∨ (p1 ∨ (True ∧ (p4 → True)))) ∨ (p4 ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160720550312158273590864195157 : (((False ∨ ((p5 → p3) ∧ ((False ∨ p4) ∧ p1))) ∨ (((False → p5) ∨ ((p3 → False) ∧ p3)) → p1)) → (((p5 ∨ (p2 ∨ False)) ∨ True) ∨ False)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- False on the left can always be used.
        apply False.elim h9
      case inr h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h11 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157992455128921263440033362777 : (((((False ∨ p5) → True) ∨ (True ∨ (p3 ∨ True))) → (p2 → (p3 ∧ ((p5 ∧ (p4 → True)) → p2)))) ∨ (((p2 → p2) ∨ (p4 → p2)) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315862768300746988934074210829 : (p3 ∨ ((p4 → False) → (((p3 ∧ True) ∧ ((p1 ∧ (p4 ∨ (p2 ∧ True))) ∧ (True ∧ (p3 → (p2 ∧ p3))))) ∨ ((p5 ∧ True) → (p5 ∨ p2))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39548922543791459503053979735 : (((False ∨ (p5 → (((((p1 → (((p3 ∧ True) ∨ False) ∧ False)) ∧ ((True → p5) ∨ (p1 ∧ True))) ∧ True) ∧ (p1 ∧ p2)) → p3))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336299301521145478036817082402 : (p1 → (((p5 ∧ ((p1 ∧ (p5 → True)) → p1)) ∧ (p2 → ((True → (False ∧ (((False → p2) → (p3 → False)) → False))) ∨ (False ∨ p2)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729107922987652084178666721140 : (((((True → p5) ∧ p1) → (((p5 ∨ (p2 → p1)) ∨ (((p5 ∨ p3) ∧ ((True ∧ False) ∧ p4)) ∧ p3)) → (p3 ∨ (p4 ∨ (p4 ∨ True))))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      let h5 := h1.left
      let h6 := h1.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h1.left
      let h9 := h1.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h11.left
    let h14 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h14.left
      let h17 := h14.right
      -- Conjunctions on the left can always be decomposed.
      let h18 := h16.left
      let h19 := h16.right
      -- False on the left can always be used.
      apply False.elim h19
    case inr h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h14.left
      let h22 := h14.right
      -- Conjunctions on the left can always be decomposed.
      let h23 := h21.left
      let h24 := h21.right
      -- False on the left can always be used.
      apply False.elim h24
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115770862055573949048877827128 : (((p1 → (p5 ∨ (p1 ∨ (p2 ∧ p2)))) → ((p1 ∨ (((p3 ∨ p1) ∧ p1) ∨ p5)) ∧ (p1 ∧ (False ∨ ((p5 → False) ∧ p1))))) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191879172484083031179091687231 : ((p4 ∨ (p2 ∧ (((False → p1) ∨ p1) ∧ (True ∨ p4)))) ∨ (((p1 ∧ (((p3 → (p2 → p5)) → (p5 ∨ p1)) ∨ p2)) ∧ p2) ∨ (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174633440443448606247371498939 : (((True ∨ ((True → False) → p3)) → ((p1 ∧ (True ∨ ((p1 → p1) ∧ p1))) ∧ p3)) → ((p1 ∨ p3) → (p4 → (((p5 → p2) → p5) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h6 : (True ∨ ((True → False) → p3)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h7 := h1 h6
    -- We need to get the left conjuct of h7 based on <expert-advice>.
    let h8 := h7.left
    -- We need to get the left conjuct of h8 based on <expert-advice>.
    let h9 := h8.left
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57074801039367648910414133085 : ((((True ∧ True) ∧ p4) ∨ ((p3 → ((p1 ∨ (True ∧ False)) ∨ (((p1 ∨ (p3 ∧ p3)) ∨ False) → ((p3 → True) → p1)))) ∧ (p2 → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323937432742567931330041640061 : (p5 ∨ (((True ∧ p1) ∨ ((p4 ∨ ((True ∧ p5) → ((p1 ∨ (p2 → False)) ∨ p3))) ∨ False)) → (((p5 → (p4 ∨ p1)) → (p4 → False)) ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
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
      -- False on the left can always be used.
      apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165248388377590903116090209890 : (((p5 ∨ ((p1 ∨ (p1 → (p3 ∧ (p1 ∧ ((p5 ∨ p1) ∧ False))))) ∨ p2)) ∨ (p1 ∧ p3)) ∨ (False → (p5 ∧ ((True ∨ False) → (p3 ∨ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h1
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317036107414047181260350003292 : (p3 ∨ (p4 → (((p5 → p2) ∧ ((((False ∧ (p2 → p3)) → ((((p4 → ((p3 ∨ p4) ∧ p3)) ∨ False) ∨ p1) → p5)) → p1) ∨ p3)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218315461028461207732154665084 : (((True → False) ∨ (False ∧ p1)) → ((p4 ∨ p1) ∨ ((((p4 ∨ p2) ∨ ((False → (False ∨ (p5 ∨ p5))) → (p5 → p4))) ∨ (p1 → False)) → False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h4 := h2 h3
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178892995572364472449717896881 : (((True ∨ p5) ∧ (p5 → ((False ∨ False) ∧ ((True ∨ p5) → (p4 → p1))))) ∨ ((True ∨ (p2 ∧ p3)) → ((p1 → p3) ∨ ((True → False) → False)))) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h9
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40995807089501918034840326824 : ((((True → ((p1 ∨ (((p1 → ((False → False) ∨ p4)) → False) → p1)) → (((p4 ∨ p1) → (p3 ∨ False)) ∨ p2))) ∨ (p3 ∨ p4)) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208099098611597759703149723550 : ((((True ∨ p1) ∧ True) → (p4 → False)) → (((False ∨ (p4 → ((p4 → p2) ∧ p1))) → ((((True ∨ p4) ∨ (p1 ∧ p5)) → True) → p2)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206868968552953233454981484802 : (((((p1 → p2) → True) ∧ p4) ∧ p2) → (((True ∧ ((p5 ∨ ((False ∨ p4) ∧ (((p1 ∧ (False ∧ p3)) ∨ p1) → p5))) → p2)) ∨ p3) ∨ True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208068306752208427952220668697 : (((p5 ∨ (p3 ∨ p2)) ∨ (True → p1)) → (((((True ∧ True) → ((p3 → False) ∧ (False → (p1 ∨ p1)))) → (True ∨ p5)) → p3) ∨ (True ∨ p3))) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
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
theorem thm_5_vars_263569244162632453205406359023 : (True ∧ ((((p2 → p5) ∧ ((p5 → p5) ∧ (p5 ∧ p4))) ∧ (p4 ∧ (True → ((p1 ∨ p3) → (p1 ∧ False))))) ∨ (True ∨ ((p3 ∧ False) → False)))) := by
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
theorem thm_5_vars_177673405897496249856138713095 : (((((((True ∧ p5) ∨ (p1 ∨ p1)) ∨ p5) ∧ (p3 ∨ p3)) → p5) ∧ p5) ∨ (((False ∧ p5) → p2) ∨ ((((p3 ∧ True) → p5) ∨ p1) ∧ True))) := by
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
theorem thm_5_vars_159951698636323040650669392870 : ((((p5 ∨ ((p1 ∨ ((p1 ∨ (p1 → (p5 ∨ p1))) ∨ False)) ∧ (p2 ∨ False))) ∨ (p1 ∧ False)) → p4) → ((p2 → p5) → ((p2 ∨ False) → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178111472374643443183067707025 : (((((((p1 → p1) ∧ (p5 → True)) → p3) ∨ p4) → (False → p2)) → p1) ∨ ((p2 ∧ p4) ∨ ((True ∨ p4) ∨ (p3 → (False → (p3 ∧ p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258354452203422281126531708715 : ((p5 ∨ False) → ((((p3 ∨ p5) → ((p3 ∨ p2) ∨ p2)) ∨ (p3 ∧ ((((False ∨ p3) → p3) ∧ (p2 ∧ p1)) ∨ p1))) ∨ (p1 ∨ (p2 → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41547607182427869924968206599 : ((((False ∨ ((p3 → False) ∧ ((p2 ∨ (p4 ∧ p2)) ∨ p3))) ∨ (True → (((p5 ∨ p2) → ((False → False) ∧ False)) → (p4 ∧ p4)))) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114010857281771128757402468462 : ((((p5 ∧ (p5 → (p3 ∨ (((True ∨ (p2 → p2)) ∧ ((p3 ∧ p5) ∧ (p3 ∨ p5))) → p4)))) ∧ p2) ∨ (True ∨ (True ∧ False))) ∨ (p1 → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50125797598107310373114207548 : (((p3 ∨ (((p3 ∨ ((p1 ∨ (False ∧ p4)) ∨ ((p2 ∨ p1) → p4))) ∧ (p1 ∧ p1)) → (False ∨ True))) ∧ ((p1 → (p1 ∧ p2)) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229031482992157310583314405706 : ((p5 ∨ (False ∨ False)) ∨ ((p2 ∧ (((((p2 ∧ p5) ∨ p3) → (p3 ∧ ((p1 → p5) ∨ (p4 ∧ (p3 ∨ (p4 ∨ False)))))) ∨ p5) ∧ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322321264464998374232245230642 : (p5 ∨ ((((p1 → (p4 → p5)) ∨ ((((p2 → p4) ∨ (((True → p2) → ((p5 ∧ p2) → True)) ∨ False)) → True) → p2)) ∧ (p3 ∨ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158936080011956023794695000279 : ((p2 ∨ (((True ∨ ((False → (True ∧ p2)) → (((p1 ∨ p1) ∨ p3) ∨ p3))) → (False → p5)) → p4)) ∨ (((p3 ∨ True) ∧ (p3 ∧ False)) → p4)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h3.left
    let h9 := h3.right
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610818880379404839686308644978 : (((((((p3 ∨ ((((False → (p4 ∧ (p2 → p2))) ∧ p1) → True) ∧ p3)) ∨ p1) ∧ ((True ∨ ((p2 ∧ p1) ∧ False)) → p5)) → p1) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194263434929288404638276058563 : ((p5 → (((True → False) ∨ (False → (True ∨ True))) ∨ p3)) → (p4 ∨ (p3 → (((((p5 ∧ p3) ∨ ((False → p4) → p5)) ∨ p1) ∧ p2) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704235755203725431816652276439 : (((((((p4 → p5) ∧ p3) → (p4 ∧ False)) → (p5 → p1)) → ((True ∧ ((p5 ∧ True) → (((p4 ∧ False) ∨ (p1 ∨ p2)) → p2))) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_663044186410070893842375520944 : (((((False → (p1 ∧ p5)) → (p1 ∧ ((((p4 → p5) → ((p1 → p5) → p4)) ∧ p2) ∨ (p4 ∨ ((p1 ∨ p2) ∨ p4))))) → (True → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_94994697315769368695740195984 : ((p4 ∧ (((p2 ∨ p4) → (p4 → (((p1 ∨ (p5 → (p1 ∧ (True ∧ p1)))) ∧ p2) ∧ ((p2 ∨ (p3 → p2)) ∧ (p4 ∧ p5))))) ∧ p3)) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : (p2 ∨ p4) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h9 := h7 h8
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- One of the premise coincides with the conclusion.
  exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244041649262824187290731701911 : ((True ∧ p2) ∨ ((True ∧ p5) → (p5 ∧ (((False ∧ p2) ∧ p3) ∨ (p2 ∨ ((p1 ∧ (p2 ∧ (True → (p4 → (p5 ∨ True))))) → (p4 → p4))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h9.left
  let h11 := h9.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324112886971638927826395162023 : (p5 ∨ ((((p1 ∧ p5) ∧ True) ∧ (((p4 ∨ (p1 → False)) → True) → False)) → (p2 ∨ ((False ∨ (((p4 → p4) ∧ False) ∧ p1)) ∨ (False ∨ p4))))) := by
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
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h8 : ((p4 ∨ (p1 → False)) → True) := by
    -- Implications on the right can always be decomposed.
    intro h9
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h10 := h3 h8
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_651459122386779054795829131407 : (((((p1 ∨ (True ∧ p3)) → (True ∧ ((p2 ∨ p5) ∧ ((((p1 ∨ (True → True)) ∨ (True ∧ (p3 → True))) → True) → p4)))) ∧ (p1 ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208308488402436530431146500025 : (((p5 ∨ p4) ∧ (p5 ∨ (p1 ∧ p2))) → ((p2 ∨ p1) ∨ (((p5 ∧ p1) → ((False ∨ p3) ∧ ((p2 ∨ False) → p5))) ∨ ((False ∨ True) → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- False on the left can always be used.
        apply False.elim h7
      case inr h8 =>
        -- One of the premise coincides with the conclusion.
        exact h5
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- False on the left can always be used.
        apply False.elim h15
      case inr h16 =>
        -- One of the premise coincides with the conclusion.
        exact h13
    case inr h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68748743901213399446510078754 : ((p4 → (((((p2 ∨ p4) ∧ (p5 ∨ (True ∧ (p2 ∨ p3)))) ∧ (p1 → p3)) → (p1 ∨ p4)) → (((p1 ∨ p4) ∧ (p2 ∧ p4)) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265791869596336267522798093348 : (True ∧ (p4 ∨ ((p4 → p3) → ((p5 ∨ p1) → (p1 → (((False ∨ (p1 ∨ p5)) ∧ (True ∧ (p1 → (((p2 ∨ p3) ∧ p3) ∨ p1)))) ∨ False)))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_735457841555127560946923131712 : ((((p4 ∨ p3) ∧ (False ∧ ((((True ∧ p5) ∨ p1) ∨ False) ∨ (p3 → (True ∨ (((p2 ∨ p5) ∨ (p2 → (p4 ∧ (p4 ∧ p1)))) → p2)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_823010787529780758374558467977 : ((((((True ∧ ((True ∧ (False ∨ False)) ∧ p5)) ∨ True) → ((((p2 ∨ p2) → ((False → (True → p1)) ∧ (p4 ∧ p4))) ∧ False) ∧ p3)) ∧ p5) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((True ∧ ((True ∧ (False ∨ False)) ∧ p5)) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225896367178684449075002592813 : (((p1 ∧ p2) ∨ p3) ∨ ((((False → p1) ∧ ((p4 ∧ (p2 → p3)) ∧ p4)) ∨ (p5 → (((False → p2) ∨ p2) ∧ p4))) ∨ (True ∧ (p2 → p2)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305039407216709210951460264261 : (p1 ∨ ((p4 → ((p3 ∧ ((((((p4 ∨ True) ∨ (p4 → False)) → p3) ∧ p5) ∧ (True ∨ p4)) → p2)) ∨ (p1 ∧ True))) ∨ ((p5 ∧ p1) → p5))) := by
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
theorem thm_5_vars_179067689268618126597771624530 : ((True ∧ ((p1 ∧ ((((p1 ∨ p3) ∨ p4) ∨ p4) ∨ True)) ∧ (p5 ∧ True))) ∨ (((False ∨ (p5 ∧ ((p3 ∧ p3) → False))) ∨ (p2 ∧ p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353579999315517906712525563831 : (p4 → (p3 ∨ (p5 ∨ ((((p2 ∨ True) ∨ ((True → p1) → p1)) → False) ∨ ((False → (p3 → (True ∧ ((p1 → p2) → (p4 ∨ p5))))) ∧ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190890361770790238679039876627 : (((p1 ∧ ((p4 → (p2 → p4)) ∨ False)) → (p3 ∨ p2)) ∨ (False → (((False ∨ (p2 ∨ True)) ∨ (p1 → True)) ∨ ((p4 ∧ p2) → (p1 → p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_162865313271000351632365475056 : ((((p1 ∨ (True ∧ ((p1 ∨ p2) ∧ p2))) ∧ (p5 ∧ (False ∨ (True → True)))) ∨ (False → False)) ∧ ((False ∧ True) → (((p1 → p1) ∧ p1) → p3))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h2.left
  let h7 := h2.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178265631517091325449030701833 : ((((p5 → (True ∧ ((p5 ∨ p2) → True))) → (p1 ∧ p4)) ∧ (p2 ∨ p2)) ∨ (((True ∧ ((((p5 → False) ∨ p3) ∧ False) ∨ p3)) ∧ p3) → p3)) := by
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
      apply False.elim h8
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h8
  case inr h11 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612776582403516375096362617948 : ((((((p4 → (p5 ∨ p3)) ∨ ((p5 → p4) ∧ (p1 ∧ ((((True ∧ (p1 ∨ p2)) ∨ False) ∧ (p2 ∧ p2)) ∧ False)))) ∨ (p3 ∧ p1)) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336876800871988555802487088783 : (p1 → ((True → ((p3 ∨ ((p5 ∨ (True → (((False ∨ p4) ∨ True) → ((True ∧ p3) ∨ (((p3 ∨ p5) → p4) ∨ p1))))) ∧ p5)) ∧ False)) → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191031602246736164206616475501 : (((((False ∨ p3) ∨ p3) ∨ p1) → ((p4 ∨ p5) ∨ p1)) ∨ (p5 → ((True ∧ True) ∧ ((False → False) ∨ ((False ∧ (p3 ∧ p1)) → (p4 ∧ p5)))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_734517792205858874003583241449 : ((((p1 ∨ False) ∧ (p2 ∨ ((((p5 ∨ ((p3 → (p1 ∨ p5)) ∨ (p4 ∧ (False ∨ p4)))) ∧ True) ∨ (p4 → p3)) → ((p4 ∨ p4) → p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608062347479492490143938739458 : ((((((((p5 ∨ (((p4 → (p1 → p4)) ∨ (((True ∨ (p1 ∧ p1)) ∨ (p3 ∨ p2)) ∨ p4)) → p4)) ∧ p4) ∨ True) ∧ p3) ∨ True) ∨ p4) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_219838155676991340080821022663 : ((p3 → ((p5 ∧ p2) → p4)) → (((p5 ∨ (p4 → p3)) ∨ (True ∨ (p2 ∧ ((p2 → False) ∨ ((True ∧ True) ∧ p4))))) ∨ (p1 ∨ (p3 ∨ p1)))) := by
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
theorem thm_5_vars_699121616052294892100919610307 : ((((True → ((((False → (p4 → p2)) ∧ (p1 ∧ p2)) ∧ True) ∨ p4)) ∨ ((p5 ∨ (p1 → (p2 → (True ∨ p4)))) ∧ (p5 ∧ (p2 ∧ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49309949261824455553308340821 : (((p1 ∨ (p2 → (((p2 ∨ p1) ∧ (p3 ∨ (p1 ∧ (p3 ∨ p4)))) ∨ (p2 ∨ (p3 ∧ (p5 ∨ (p3 → p4))))))) ∨ (p5 → (p5 ∨ False))) ∨ p5) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157686886703969705125534255324 : (((p3 ∨ (p4 ∨ (p3 ∧ (p3 ∨ ((((p1 → p3) ∧ p4) ∨ p3) ∧ p1))))) ∨ (True ∧ (p1 ∧ p5))) ∨ (p3 ∨ (((True → p4) ∨ p1) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_96543957676387426077880237981 : ((False ∨ ((p3 ∨ True) → (((p1 ∧ (((True ∧ (p1 ∧ p4)) → ((((p3 → (p4 ∨ p5)) → False) ∨ p2) ∨ p5)) → p2)) → p1) ∧ False))) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : (p3 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- We need to get the right conjuct of h5 based on <expert-advice>.
    let h6 := h5.right
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214738529056946571041637150550 : (((p3 ∧ p3) ∨ (p4 ∧ True)) ∨ (((p5 ∧ ((((p4 ∨ ((True ∧ True) ∧ (p4 ∨ p4))) ∨ (p2 ∧ (False → False))) ∨ p3) ∨ False)) ∨ True) ∧ True)) := by
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
theorem thm_5_vars_39854349013929703923980606520 : (((p1 → (p1 ∧ ((p2 ∨ (((p1 ∨ (((p2 → (False ∧ p4)) → ((p2 ∧ p2) ∨ p3)) → p2)) ∨ p4) → (True → False))) ∨ p1))) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40204442032097183652925793183 : (((((p2 → p5) ∧ (((p2 → ((((p2 ∧ False) → p5) ∧ ((p3 ∧ p4) → (True ∨ (p2 → p3)))) → p1)) ∧ False) ∨ p4)) ∧ p2) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149038285885789055819913096348 : (((p5 ∧ (p1 ∨ p3)) ∨ (((False → p4) → (p3 ∨ (p4 ∨ p2))) ∨ (False ∨ ((True ∨ (p5 ∨ p3)) ∨ True)))) ∨ ((True ∨ (p2 ∨ p3)) → p2)) := by
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
theorem thm_5_vars_158452003670473446612858120800 : (((p5 ∨ p4) ∨ ((p2 ∨ (False ∨ (p5 ∧ p2))) ∧ ((p5 ∧ ((False ∧ p3) ∨ (p2 → p1))) → p4))) ∨ ((p4 → (False ∨ (p2 → p2))) ∨ p4)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352090394820916578731170842644 : (p4 → (((((False ∧ p4) ∨ p1) ∨ p1) ∧ False) ∨ (p5 ∨ (p3 → (p2 → ((p3 ∧ ((((p1 ∨ p4) ∧ (True ∨ p5)) ∨ p4) → p1)) → p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62552351396755895579664438427 : ((p3 ∧ (p3 ∨ ((p1 ∨ (True → (p2 → (False ∨ p1)))) ∧ ((p3 ∧ ((p3 → p3) ∧ p4)) ∧ (p3 ∧ (((False ∨ p3) ∧ True) ∧ True)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200724868390887593180845494279 : ((p3 ∧ ((((p4 ∨ p3) → True) → False) ∨ p2)) → ((p3 ∧ p3) ∧ ((p1 ∧ ((p5 ∧ (p5 → p2)) ∨ p5)) ∨ (p3 ∨ (p3 ∨ (False ∨ p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51942802003057667154574831722 : (((((p4 ∨ True) → (((True → p2) ∨ p4) ∧ p4)) → ((False ∧ (p3 ∨ p1)) ∧ False)) ∨ (p2 ∨ ((False → p2) ∨ ((True → p5) → p3)))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_266051527194213593260128681819 : (True ∧ (p1 → (p5 → ((False → p5) → (((True ∨ p5) ∨ True) → ((p1 ∧ (((p4 ∧ (True ∨ p2)) ∨ p4) ∨ (False → (p1 ∧ True)))) ∨ p5)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_103229325857874345753612530052 : (((p2 ∧ ((((p3 ∨ False) ∨ (p4 → p5)) ∨ p1) ∨ (p3 ∨ (True ∧ ((p5 → (p3 → p5)) ∧ ((p2 → p5) ∧ p2)))))) ∨ True) ∧ (p2 → True)) := by
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
theorem thm_5_vars_41712319179378336793695066232 : ((((True → ((p5 → p2) ∧ (False ∧ p2))) → (p1 ∧ ((((p1 ∧ (p3 ∧ (p2 ∨ ((p3 ∨ True) ∨ p4)))) ∧ p1) ∧ p4) ∧ True))) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56562626352645439812876403089 : (((p5 ∨ ((p4 → p1) ∧ True)) → ((True ∧ (False ∨ ((False ∧ (p5 → p4)) ∨ True))) ∧ ((p3 ∨ (((p1 → p1) ∨ False) → p1)) ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205664552231925000008134474275 : (((p1 ∨ p1) ∨ (p5 ∨ (p2 → p3))) ∨ ((((p5 → (True ∨ p4)) → p2) ∨ (((p4 ∨ (p2 ∨ True)) ∧ False) ∨ True)) ∨ ((p2 ∧ False) ∧ False))) := by
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
theorem thm_5_vars_38877901633574076713479451283 : (((((p3 ∧ p1) ∧ True) ∨ ((((p3 ∨ (p5 → False)) → (p1 ∧ (False ∨ p4))) → (p3 ∧ ((True ∧ p5) ∨ (False ∧ p1)))) ∧ p5)) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350979837109070425263712687638 : (p4 → (((False ∨ False) ∧ (p4 ∧ (p1 → ((True ∨ (p3 ∧ (False ∨ ((p3 ∨ (p5 ∧ (False ∨ p3))) ∨ p1)))) → (p4 → False))))) ∨ (True ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_188290429038803524691938969522 : (((p5 ∨ (((p4 ∨ p5) ∧ False) ∨ (p1 → p1))) ∨ True) ∧ ((p5 ∧ (p1 → p1)) ∨ ((p3 → False) ∨ (True ∧ (p2 ∨ ((True ∨ p2) ∨ p1)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185443545707498201708033875883 : ((False ∨ ((p5 ∨ p4) ∧ ((True ∧ True) ∧ (p4 → (p5 ∨ p3))))) ∨ ((p4 ∧ p2) → ((True → (p3 ∧ p5)) → (((p5 ∨ p3) → True) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_640351200530181342940350105724 : (((((p3 → (p2 ∨ False)) → ((False → p1) → ((((p4 ∧ p5) ∨ p5) ∧ p4) ∧ (((p5 → False) → (p3 → p4)) ∧ (p5 → p1))))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68484521372259382862755136988 : ((p3 → (False ∨ (((((((p5 → ((p1 ∧ p1) ∨ ((p1 → p4) ∨ p4))) ∨ p3) ∨ (p4 ∧ True)) ∧ (False ∨ p1)) → p5) ∨ True) ∨ p5))) ∨ False) := by
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
theorem thm_5_vars_245022447581893392381482501628 : ((p1 ∧ p4) ∨ (p1 ∨ ((p4 → (((True → p5) → ((p3 → False) → (False ∧ p5))) → p2)) → ((p5 ∨ p2) ∨ ((p4 → (p4 ∨ True)) ∨ p1))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_653926864349792846754454147950 : ((((((p1 ∨ p2) ∨ (((p3 → p1) ∧ ((((p2 → (p5 ∧ (p3 ∨ False))) → p5) ∨ p2) → (p5 ∧ p3))) ∨ True)) ∧ p1) ∨ (True → True)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112350507925078198207666669085 : (((((((((((p1 ∧ p1) → (True → (((p1 ∧ p3) → p2) → p5))) ∧ p3) ∧ p3) → True) ∨ False) → p5) ∧ p2) ∧ p2) → p3) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58030958145020574351148181202 : (((True ∧ p4) ∧ ((p4 ∨ (p5 ∧ ((p4 ∨ p4) ∨ (((p1 ∨ p3) → False) ∧ False)))) ∧ ((p4 ∨ (p5 → ((False ∨ False) ∨ p3))) ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199373868667339945796010179245 : ((((False ∧ (p2 ∨ p5)) ∨ (p5 → p3)) ∨ False) → (p1 ∨ ((p1 ∧ p2) ∨ ((((p5 ∨ p5) ∨ p2) ∨ ((p2 → p5) → (False → p2))) ∨ p5)))) := by
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
      -- False on the left can always be used.
      apply False.elim h4
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h8
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329290952775495640975689635167 : (True → ((False ∧ (p2 ∨ p4)) ∨ (p3 ∨ (p5 ∨ ((True ∧ True) ∨ ((False ∨ False) → ((False ∧ (p4 ∧ p3)) ∧ (p1 ∧ ((p3 ∧ p3) → False))))))))) := by
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
theorem thm_5_vars_53211158006261275439807244764 : ((((p5 ∨ (p4 ∧ (False → (p4 → False)))) ∧ ((p2 ∧ p4) ∧ p4)) ∨ ((p4 → True) ∧ (((False ∨ p2) ∨ ((True → True) ∨ p5)) → True))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679801221103075530867692368420 : ((((((p1 ∧ p1) → (((((p1 → ((False → True) → (p3 ∧ p1))) ∧ p4) ∨ p5) ∨ p1) ∨ p5)) ∨ True) → (p1 ∨ ((p2 → p1) ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62567843034511774836056477927 : ((p3 ∧ (True → (((p3 ∧ True) → (False ∧ ((p1 ∨ ((False ∧ p4) ∨ ((p3 ∧ (p5 → p2)) ∧ False))) ∨ (p2 → p2)))) ∧ (True ∨ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197520721411574201094805787723 : (((p4 → (p1 ∧ (p1 → False))) ∧ (True → p3)) ∨ (((True ∨ p4) ∧ (p2 → p1)) ∨ ((p4 ∨ True) ∧ (((p4 ∨ p3) → (False ∧ p2)) ∨ True)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



