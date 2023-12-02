variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113038242105422792636328952195 : (((False ∨ ((p1 ∧ ((p1 → False) ∧ (p4 ∧ p3))) ∧ (True ∧ ((((p1 → p3) ∨ (p4 → p2)) ∨ p5) ∨ (True → p1))))) → p5) ∨ (True ∧ p2)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h5.left
    let h13 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h16 =>
          -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
          have h17 : p1 := by
            -- One of the premise coincides with the conclusion.
            exact h6
          -- We have shown the premise of h8, we can now drive its conclusion.
          let h18 := h8 h17
          -- False on the left can always be used.
          apply False.elim h18
        case inr h19 =>
          -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
          have h20 : p1 := by
            -- One of the premise coincides with the conclusion.
            exact h6
          -- We have shown the premise of h8, we can now drive its conclusion.
          let h21 := h8 h20
          -- False on the left can always be used.
          apply False.elim h21
      case inr h22 =>
        -- One of the premise coincides with the conclusion.
        exact h22
    case inr h23 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h24 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h25 := h8 h24
      -- False on the left can always be used.
      apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198755598662294259643623399220 : ((True → (((p4 ∧ p5) → True) → (p2 ∨ p5))) ∨ (p1 → (p4 → (((((p3 ∨ p3) → ((False ∨ p1) → True)) → (p1 ∧ p2)) ∧ p1) → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_145896455249584495320656533319 : (((False → p4) → ((((True ∨ (p4 ∨ p4)) → (((True → False) ∧ True) ∨ p2)) ∨ p2) ∨ (p1 → (p2 → p2)))) ∧ (((p3 ∨ False) → True) ∨ p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303759090873432389242020498497 : (p1 ∨ (((((((((p4 ∧ p3) ∧ True) ∧ ((p4 ∧ False) → True)) → p2) → True) → (p2 ∨ (p2 → p1))) → ((p2 → p4) ∧ p1)) ∨ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140746017865526927902195782553 : (((((p4 ∨ (p4 ∨ False)) ∨ ((p4 ∨ p3) ∨ p4)) → (p3 → (False ∨ p3))) → (p3 ∧ ((p5 → (True → p2)) ∧ False))) → (p2 ∨ (p1 → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115214251540715949692221792809 : (((p4 ∨ ((((p1 ∧ p1) ∨ p3) ∧ p2) ∨ (p3 → p4))) ∧ (((p2 ∨ p5) ∨ p1) → ((p2 → (p3 ∨ p4)) → (True ∧ p5)))) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_730649772021925089102521924773 : ((((p2 ∧ (p5 → True)) → ((p1 → (p4 → (p2 → ((p2 → p4) ∨ ((False → (p3 → ((p2 ∨ (False ∧ p1)) → p2))) ∨ p2))))) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171530764705629174825455891947 : ((((((p1 ∧ ((p3 ∨ p3) → p1)) → (p2 ∧ p3)) ∨ (True ∨ p1)) ∨ p1) ∨ p2) ∨ (p4 ∧ ((p2 → (p3 ∨ (p2 → (p3 → True)))) ∨ True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_131014640276105302317506489982 : ((((p2 → ((p5 ∨ ((False ∧ p1) ∨ p1)) ∧ False)) ∧ p5) ∨ (((False ∨ (((p2 ∨ False) → True) ∧ p4)) → p2) → True)) ∧ ((p5 ∨ False) → p5)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174135435651928963968497512884 : (((((p2 → ((((True ∨ p4) ∧ False) ∨ True) ∧ p2)) ∨ p4) ∨ True) ∨ (True ∧ p1)) → (((True ∨ p5) → p1) ∨ (False → (False → (False ∧ False))))) := by
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
        -- Implications on the right can always be decomposed.
        intro h5
        -- Implications on the right can always be decomposed.
        intro h6
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- False on the left can always be used.
        apply False.elim h6
        -- False on the left can always be used.
        apply False.elim h6
      case inr h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h8
        -- Implications on the right can always be decomposed.
        intro h9
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- False on the left can always be used.
        apply False.elim h9
        -- False on the left can always be used.
        apply False.elim h9
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- Implications on the right can always be decomposed.
      intro h12
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h12
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h16
    -- Implications on the right can always be decomposed.
    intro h17
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h17
    -- False on the left can always be used.
    apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_81939645155098417420624134656 : ((((p1 ∨ (((p5 ∨ (p5 ∧ (p2 ∨ p3))) ∧ ((False ∨ p1) → p1)) ∨ True)) ∨ (p3 ∨ (p3 ∨ (True ∨ p4)))) → ((False ∧ False) ∧ p4)) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p1 ∨ (((p5 ∨ (p5 ∧ (p2 ∨ p3))) ∧ ((False ∨ p1) → p1)) ∨ True)) ∨ (p3 ∨ (p3 ∨ (True ∨ p4)))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230280590452964796081881283029 : (((False ∨ p5) ∧ p1) → (((((((p3 → (p4 ∧ False)) → False) → p2) → ((p1 → (p2 ∧ p4)) ∧ p4)) ∨ p5) ∨ ((p3 ∧ p5) ∧ True)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160328090391588566783961057901 : ((((p2 → False) → (((p2 ∨ (((False → p2) ∨ p2) → (p4 ∨ p5))) → p4) → True)) → (p1 ∧ False)) → (False ∧ (((p5 → p3) ∨ True) ∧ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p2 → False) → (((p2 ∨ (((False → p2) ∨ p2) → (p4 ∨ p5))) → p4) → True)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : ((p2 → False) → (((p2 ∨ (((False → p2) ∨ p2) → (p4 ∨ p5))) → p4) → True)) := by
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h7
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136682746567128764771948268792 : (((p2 → (p2 → True)) → (p3 ∧ (((False → p5) ∧ (p4 ∧ (p5 ∧ p4))) ∨ (((True → (p5 ∨ p1)) ∨ p3) → p1)))) ∨ ((p5 → True) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303907638567697468235047897786 : (p1 ∨ (((p4 → ((p3 ∧ (((p5 → p3) ∨ (p1 ∧ p3)) → False)) ∧ (False ∨ p3))) → ((True → (p4 ∧ (False ∧ True))) → (p5 ∨ p2))) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312996357124954491172430148252 : (p3 ∨ ((((False ∨ ((p5 ∧ True) → ((((p2 ∨ p3) ∨ ((p2 → (p5 → p3)) ∨ ((p5 ∨ False) → p1))) → p1) ∨ p1))) ∨ False) ∨ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358136814533189820790171202881 : (p5 → (p2 ∨ (p5 ∧ ((p3 ∧ False) ∨ (((True ∨ True) → ((p4 ∧ p1) ∨ (True → ((False ∨ (p2 ∨ p3)) → (False ∨ (p4 ∧ p3)))))) ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187668129943927190668334241254 : ((True → ((p4 ∧ ((p2 ∧ p1) ∨ p4)) → (p4 ∧ (p3 ∨ p4)))) → ((((p3 → (p3 → False)) ∨ (p3 → p2)) ∨ True) ∨ (p1 → (p1 → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_587737029081289634318848667759 : ((((((True → ((((((((p3 ∨ p2) → (True → False)) ∧ ((p3 → p2) ∨ p1)) → p5) ∧ p2) ∨ p3) → True) ∨ p1)) → p1) ∨ p1) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329783360552151218780070142119 : (True → (True ∧ ((False ∨ p2) ∨ ((((p1 ∧ ((((p2 → p1) ∨ p5) ∨ p1) ∨ p3)) ∧ ((p4 ∧ p1) ∧ (p3 ∧ p5))) ∧ False) ∨ (True ∨ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358173493843648364083095583772 : (p5 → (p3 ∨ (((((((False → p5) → False) ∨ p2) ∧ (True → p1)) ∨ p2) ∧ (p2 ∧ (False ∧ (True ∨ False)))) ∨ (p4 → ((True ∨ False) → p4))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64852240497371687336096692110 : ((p2 ∨ (((p4 → ((((p3 ∨ p3) → (((p3 → True) ∧ p2) → ((p3 ∨ True) ∨ p5))) ∨ (p2 ∨ False)) ∨ p5)) → p3) ∧ (p2 ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656320703445567699091299238093 : (((((((p3 ∨ p2) ∨ p4) → ((p5 → ((p3 ∨ True) → p4)) → False)) ∨ (((p3 ∧ (p3 → False)) ∨ (p1 → p4)) → p4)) ∨ (p3 → True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159327363249651596825988303931 : ((p5 → ((p3 ∨ p4) → ((((p3 → p1) → ((((p4 ∧ p1) ∨ p2) → p3) ∧ p3)) ∧ False) ∧ False))) ∨ (p4 → (p5 ∨ (p1 ∨ (p4 ∨ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344483972110495894318431233028 : (p2 → (True → (((((p2 ∧ ((p1 ∨ p4) ∧ ((p5 ∨ p1) → (p4 ∧ p3)))) ∨ False) ∨ (False ∨ (p2 ∨ True))) ∨ p2) ∨ ((p4 ∧ p4) ∧ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58548530448770774390877219783 : (((p5 ∨ p5) ∧ ((((True ∧ (False → False)) ∧ p2) ∨ (False ∨ p2)) ∧ ((False ∨ ((p5 ∧ p5) ∧ (False ∧ p1))) ∨ (p5 → (p2 ∧ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117745975815613200519661393549 : ((p4 ∧ ((((p2 ∧ ((((True → True) ∨ (False → p3)) → p4) ∧ ((False ∧ p4) ∧ (p2 ∨ (False → p4))))) ∨ p5) ∨ True) ∨ p5)) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319419272105412182833848035708 : (p4 ∨ (((((p4 ∧ ((p2 ∧ False) ∧ p3)) ∧ (p5 → p3)) ∨ p5) ∨ True) ∧ ((((False ∧ (p2 ∧ p4)) → True) ∨ True) ∨ (p3 ∧ (p3 ∧ p5))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38330671092705481450312629711 : (((((p5 → ((((p3 ∧ (p5 ∧ False)) ∨ (True → (False ∧ p2))) ∧ p5) ∨ False)) ∧ True) ∧ (False ∧ (((p5 ∧ p2) ∨ True) → p5))) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708736916753740469257761364371 : ((((((p1 ∨ p3) ∧ (p5 ∧ (p2 → p5))) → p4) → (p1 ∧ ((((False → (p4 ∨ (p5 ∧ (p4 → p2)))) ∨ p1) ∨ p1) → (p1 → False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58183181239912234821137865077 : (((p3 ∧ p3) ∧ ((p1 ∧ (((False → p5) ∨ p3) ∧ True)) ∧ ((p3 ∨ p5) → ((p3 ∧ (p4 ∧ False)) ∧ (((p4 ∧ p2) ∧ p4) → p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53512837336696838929087715276 : (((True → ((((False ∨ p2) ∧ ((p4 ∧ p3) ∧ p3)) → p4) ∧ p5)) → (p4 ∨ (False ∨ ((((False → p2) ∨ (True → p5)) ∧ True) → p5)))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h7 := h1 h6
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h11 := h9 h10
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_734620142784573013504098420522 : ((((p1 ∨ p3) ∧ (((p5 → ((True → (True ∧ p5)) ∧ (p1 → p5))) ∨ ((p4 → p1) → False)) → (p4 ∨ ((True ∧ (p5 ∨ p2)) ∨ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783953496283829086295990011788 : (((p3 ∨ ((True ∧ (p2 → p5)) → ((((p4 ∧ p4) → (p3 ∧ p2)) ∧ (p5 ∧ (False → True))) → (p4 → ((p4 → (p2 ∧ p2)) ∨ True))))) ∨ p1) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305436469521778893303146419852 : (p1 ∨ (((False ∨ (p5 → (((False ∧ ((p5 ∧ p5) ∨ p3)) ∨ p3) ∨ p1))) → (True ∧ p4)) → ((((p3 ∧ p5) ∨ p3) → True) → (p4 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255750232182358337755961427626 : ((True ∨ True) → (((((p4 ∨ (p2 ∨ True)) ∨ p4) → False) ∧ ((False → True) ∧ True)) → ((p3 → ((False ∧ ((p1 ∧ True) → p2)) ∨ p1)) ∨ p2))) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h8 : ((p4 ∨ (p2 ∨ True)) ∨ p4) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h9 := h3 h8
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h11 : ((p4 ∨ (p2 ∨ True)) ∨ p4) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h12 := h3 h11
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171521841605187386099008914055 : ((((p1 → ((p3 → (((True ∨ p1) ∨ (p5 → p3)) ∧ p4)) ∨ p3)) ∧ p3) ∨ False) ∨ ((p4 → p3) ∨ (((p2 → (False ∨ True)) ∨ p3) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173632650768384845534293760183 : (((p2 → (((((p4 ∨ p5) → (False ∨ (True → False))) ∧ True) → p2) ∧ False)) ∧ p2) → ((p3 → p5) ∨ (True ∨ (False ∨ (p1 → (p1 → p2)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309366663260523419993748356976 : (p2 ∨ ((((False → p4) → True) ∧ ((p1 ∧ (((p2 ∨ p1) ∧ p3) ∧ False)) ∨ ((p3 → (p3 → False)) → (True → (p3 → False))))) ∨ (p1 ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h5
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h8 := h6 h7
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173629942941685663478394356728 : (((p1 → ((((p1 ∨ True) ∨ (((p4 ∨ p3) ∧ False) ∨ False)) ∨ True) ∨ p4)) ∧ p1) → (p5 ∨ ((((p3 → p5) ∨ (True → p4)) ∧ p1) ∨ True))) := by
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
theorem thm_5_vars_178551847418036946397039760761 : ((((p1 → ((p5 ∨ p4) ∨ p4)) ∧ False) ∧ ((p5 ∨ (p5 → p1)) ∧ p4)) ∨ (((p1 ∧ (((False → False) ∧ p4) ∨ True)) ∨ (p1 → p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139541947341244291326549357246 : (((((p3 ∧ ((((p3 ∧ (((True ∧ p5) ∧ p4) ∧ p3)) ∨ p5) ∧ (p1 → p2)) → p4)) → p4) ∨ (True ∨ p5)) → False) → ((p1 → p5) ∧ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (((p3 ∧ ((((p3 ∧ (((True ∧ p5) ∧ p4) ∧ p3)) ∨ p5) ∧ (p1 → p2)) → p4)) → p4) ∨ (True ∨ p5)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- False on the left can always be used.
  apply False.elim h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : (((p3 ∧ ((((p3 ∧ (((True ∧ p5) ∧ p4) ∧ p3)) ∨ p5) ∧ (p1 → p2)) → p4)) → p4) ∨ (True ∨ p5)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136390871825336451240375551059 : (((p1 ∧ ((p4 ∧ p5) → p1)) ∨ ((p5 ∨ p5) ∨ ((p5 ∨ p1) → ((p1 → (((p5 ∨ p3) ∨ p5) ∧ p3)) ∨ True)))) ∨ ((p3 → p1) → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_142651044589544921303613745959 : ((p1 ∨ (((((p3 ∨ (p3 ∧ p2)) → (p5 ∧ (p5 ∧ p5))) → p5) → (p3 ∧ (False ∧ (p1 ∨ (False ∨ False))))) → p3)) → (p5 ∨ (False → p1))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49611710099300411745193383571 : (((((True ∨ ((False → p5) ∨ p5)) ∧ (p4 ∨ False)) ∧ (((p5 ∨ (p2 ∨ False)) ∧ p5) ∧ (True ∧ (p2 ∨ p1)))) → (p4 ∧ (p1 ∨ True))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    cases h5
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h3.left
      let h9 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h9.left
        let h14 := h9.right
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- One of the premise coincides with the conclusion.
          exact h7
        case inr h16 =>
          -- One of the premise coincides with the conclusion.
          exact h7
      case inr h17 =>
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h18 =>
          -- Conjunctions on the left can always be decomposed.
          let h19 := h9.left
          let h20 := h9.right
          -- Disjunctions on the left can always be decomposed.
          cases h20
          case inl h21 =>
            -- One of the premise coincides with the conclusion.
            exact h7
          case inr h22 =>
            -- One of the premise coincides with the conclusion.
            exact h7
        case inr h23 =>
          -- False on the left can always be used.
          apply False.elim h23
    case inr h24 =>
      -- False on the left can always be used.
      apply False.elim h24
  case inr h25 =>
    -- Disjunctions on the left can always be decomposed.
    cases h25
    case inl h26 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h27 =>
        -- Conjunctions on the left can always be decomposed.
        let h28 := h3.left
        let h29 := h3.right
        -- Conjunctions on the left can always be decomposed.
        let h30 := h28.left
        let h31 := h28.right
        -- Disjunctions on the left can always be decomposed.
        cases h30
        case inl h32 =>
          -- Conjunctions on the left can always be decomposed.
          let h33 := h29.left
          let h34 := h29.right
          -- Disjunctions on the left can always be decomposed.
          cases h34
          case inl h35 =>
            -- One of the premise coincides with the conclusion.
            exact h27
          case inr h36 =>
            -- One of the premise coincides with the conclusion.
            exact h27
        case inr h37 =>
          -- Disjunctions on the left can always be decomposed.
          cases h37
          case inl h38 =>
            -- Conjunctions on the left can always be decomposed.
            let h39 := h29.left
            let h40 := h29.right
            -- Disjunctions on the left can always be decomposed.
            cases h40
            case inl h41 =>
              -- One of the premise coincides with the conclusion.
              exact h27
            case inr h42 =>
              -- One of the premise coincides with the conclusion.
              exact h27
          case inr h43 =>
            -- False on the left can always be used.
            apply False.elim h43
      case inr h44 =>
        -- False on the left can always be used.
        apply False.elim h44
    case inr h45 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h46 =>
        -- Conjunctions on the left can always be decomposed.
        let h47 := h3.left
        let h48 := h3.right
        -- Conjunctions on the left can always be decomposed.
        let h49 := h47.left
        let h50 := h47.right
        -- Disjunctions on the left can always be decomposed.
        cases h49
        case inl h51 =>
          -- Conjunctions on the left can always be decomposed.
          let h52 := h48.left
          let h53 := h48.right
          -- Disjunctions on the left can always be decomposed.
          cases h53
          case inl h54 =>
            -- One of the premise coincides with the conclusion.
            exact h46
          case inr h55 =>
            -- One of the premise coincides with the conclusion.
            exact h46
        case inr h56 =>
          -- Disjunctions on the left can always be decomposed.
          cases h56
          case inl h57 =>
            -- Conjunctions on the left can always be decomposed.
            let h58 := h48.left
            let h59 := h48.right
            -- Disjunctions on the left can always be decomposed.
            cases h59
            case inl h60 =>
              -- One of the premise coincides with the conclusion.
              exact h46
            case inr h61 =>
              -- One of the premise coincides with the conclusion.
              exact h46
          case inr h62 =>
            -- False on the left can always be used.
            apply False.elim h62
      case inr h63 =>
        -- False on the left can always be used.
        apply False.elim h63
  -- Conjunctions on the left can always be decomposed.
  let h64 := h1.left
  let h65 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h66 := h64.left
  let h67 := h64.right
  -- Disjunctions on the left can always be decomposed.
  cases h66
  case inl h68 =>
    -- Disjunctions on the left can always be decomposed.
    cases h67
    case inl h69 =>
      -- Conjunctions on the left can always be decomposed.
      let h70 := h65.left
      let h71 := h65.right
      -- Conjunctions on the left can always be decomposed.
      let h72 := h70.left
      let h73 := h70.right
      -- Disjunctions on the left can always be decomposed.
      cases h72
      case inl h74 =>
        -- Conjunctions on the left can always be decomposed.
        let h75 := h71.left
        let h76 := h71.right
        -- Disjunctions on the left can always be decomposed.
        cases h76
        case inl h77 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h78 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h78
      case inr h79 =>
        -- Disjunctions on the left can always be decomposed.
        cases h79
        case inl h80 =>
          -- Conjunctions on the left can always be decomposed.
          let h81 := h71.left
          let h82 := h71.right
          -- Disjunctions on the left can always be decomposed.
          cases h82
          case inl h83 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h84 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h84
        case inr h85 =>
          -- False on the left can always be used.
          apply False.elim h85
    case inr h86 =>
      -- False on the left can always be used.
      apply False.elim h86
  case inr h87 =>
    -- Disjunctions on the left can always be decomposed.
    cases h87
    case inl h88 =>
      -- Disjunctions on the left can always be decomposed.
      cases h67
      case inl h89 =>
        -- Conjunctions on the left can always be decomposed.
        let h90 := h65.left
        let h91 := h65.right
        -- Conjunctions on the left can always be decomposed.
        let h92 := h90.left
        let h93 := h90.right
        -- Disjunctions on the left can always be decomposed.
        cases h92
        case inl h94 =>
          -- Conjunctions on the left can always be decomposed.
          let h95 := h91.left
          let h96 := h91.right
          -- Disjunctions on the left can always be decomposed.
          cases h96
          case inl h97 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h98 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h98
        case inr h99 =>
          -- Disjunctions on the left can always be decomposed.
          cases h99
          case inl h100 =>
            -- Conjunctions on the left can always be decomposed.
            let h101 := h91.left
            let h102 := h91.right
            -- Disjunctions on the left can always be decomposed.
            cases h102
            case inl h103 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h104 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h104
          case inr h105 =>
            -- False on the left can always be used.
            apply False.elim h105
      case inr h106 =>
        -- False on the left can always be used.
        apply False.elim h106
    case inr h107 =>
      -- Disjunctions on the left can always be decomposed.
      cases h67
      case inl h108 =>
        -- Conjunctions on the left can always be decomposed.
        let h109 := h65.left
        let h110 := h65.right
        -- Conjunctions on the left can always be decomposed.
        let h111 := h109.left
        let h112 := h109.right
        -- Disjunctions on the left can always be decomposed.
        cases h111
        case inl h113 =>
          -- Conjunctions on the left can always be decomposed.
          let h114 := h110.left
          let h115 := h110.right
          -- Disjunctions on the left can always be decomposed.
          cases h115
          case inl h116 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h117 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h117
        case inr h118 =>
          -- Disjunctions on the left can always be decomposed.
          cases h118
          case inl h119 =>
            -- Conjunctions on the left can always be decomposed.
            let h120 := h110.left
            let h121 := h110.right
            -- Disjunctions on the left can always be decomposed.
            cases h121
            case inl h122 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h123 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h123
          case inr h124 =>
            -- False on the left can always be used.
            apply False.elim h124
      case inr h125 =>
        -- False on the left can always be used.
        apply False.elim h125



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165216924006658694414782968952 : ((((((p4 ∧ p4) → (p3 → (p5 → True))) → p4) ∨ ((p5 ∧ p2) → False)) ∨ (True ∧ True)) ∨ ((p3 → p5) ∨ (((False ∧ True) ∨ p3) ∧ p3))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228460916621469318700123459980 : ((False ∨ (p3 ∨ p3)) ∨ (p4 ∨ ((p2 ∧ (p5 ∨ p2)) → ((((((p5 ∨ p3) → p3) ∨ True) → p4) ∨ ((p5 ∧ (True → p2)) ∧ p5)) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299110317614043440765106130144 : (False ∨ (((False ∧ ((p4 ∧ p2) ∧ (p5 ∧ ((((p3 ∧ (p4 ∧ ((p2 ∧ p3) ∨ True))) → p4) ∧ p4) → (p5 ∨ (p2 ∧ p1)))))) ∧ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147022249816031833723175859583 : (((((True ∧ ((p1 ∨ ((p4 ∨ (p3 ∧ (False ∨ p5))) → p1)) ∨ True)) ∨ p4) ∧ (p1 ∧ (True ∧ p5))) ∧ p2) ∨ (((False → True) → p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172941888638703468597454613853 : ((p3 ∧ ((p2 ∧ (False ∧ p4)) ∨ (((((p4 → p2) → p4) → p3) ∧ False) ∧ p3))) ∨ ((p2 ∨ p3) ∨ (True ∧ ((p4 ∧ p4) → (p2 → p2))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205551547700026745219102019105 : (((p4 ∨ False) ∧ (True → (p3 ∨ p4))) ∨ (((p2 ∨ (((False → (True → p2)) ∧ p1) → True)) ∨ ((True ∨ p1) ∧ (p2 → p4))) ∨ (p2 ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611068953744860254927571842799 : (((((((p2 ∨ p4) ∨ (p4 ∨ p1)) ∧ (((True → ((False ∨ ((p2 ∨ ((p1 ∨ p2) ∧ True)) ∧ p1)) ∨ p1)) → p5) → p5)) → p1) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_48863377763357824939047477993 : (((p4 ∨ ((((p5 ∨ p1) ∧ p3) ∨ True) → (((True ∨ False) → p1) → (((p5 ∨ p1) ∧ p1) ∨ (p2 → p4))))) ∧ (True ∨ (p2 → p1))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h7 : (True ∨ False) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h8 := h2 h7
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9
      -- One of the premise coincides with the conclusion.
      exact h9
  case inr h10 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h11 : (True ∨ False) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h12 := h2 h11
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h12
    -- One of the premise coincides with the conclusion.
    exact h12
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42129339756665279498315465481 : ((((p1 ∨ p3) → (p1 → ((p5 ∨ (p2 ∨ (p3 ∨ (p1 ∨ p1)))) → ((((p1 ∧ (True ∨ (p3 ∨ p5))) ∧ p3) → p1) → p5)))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175397018375963655095937007067 : ((False → (((True ∧ ((p2 → (p4 ∨ p3)) ∧ (p3 ∨ (p1 ∧ p5)))) ∧ p2) ∧ p2)) → (((((p5 ∨ (p1 ∨ p3)) ∧ p1) ∧ p5) ∨ True) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113440356873146076058256722191 : (((((((p3 → (True ∧ False)) ∨ p3) ∧ p5) ∨ (((p2 ∧ ((p3 ∧ False) ∧ (p3 → True))) ∨ p5) ∨ False)) ∨ p4) ∨ (p5 → p5)) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173460665380226203603792802672 : ((((((((p2 ∨ False) ∧ True) → (False → p4)) ∨ (p3 → p1)) → True) ∨ True) ∧ p4) → (((p4 → ((True ∨ (True ∧ p5)) → False)) ∨ True) ∨ p2)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117071659993224145293284136524 : (((True → p2) → ((p1 ∨ (False ∨ (p1 ∨ ((p1 ∨ (p4 → p5)) → p2)))) ∨ (False ∨ (p3 ∨ ((p1 ∨ True) → (p5 ∧ False)))))) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185909560241054478581764182847 : ((((p1 → ((p1 ∧ p2) → p3)) ∧ (p2 ∨ (True ∨ p2))) ∧ p3) → (p3 ∧ (p5 → ((p2 ∧ (p4 ∧ False)) ∨ (((p2 → False) → p4) ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h3
  -- Implications on the right can always be decomposed.
  intro h10
  -- Conjunctions on the left can always be decomposed.
  let h11 := h1.left
  let h12 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h13 := h11.left
  let h14 := h11.right
  -- Disjunctions on the left can always be decomposed.
  cases h14
  case inl h15 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h12
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349997587310260112262187210983 : (p4 → (((((p1 ∨ p5) ∨ False) ∧ (p5 → (False ∨ (p1 → (False ∧ (p2 → ((p4 ∨ p4) ∨ ((p4 ∧ (True ∨ p5)) ∧ p5)))))))) ∨ True) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57096603977106324300713719613 : ((((p5 ∧ True) ∧ p1) ∨ (((p2 → ((True ∧ (p3 ∧ ((True → False) → p3))) → ((p5 → ((p5 ∨ True) → p1)) ∧ p1))) ∨ p4) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133957291437232925332760107516 : (((p3 → (((p2 → False) ∧ (True → ((p5 → False) ∨ p4))) ∨ (p2 ∧ (True ∨ (((p4 ∨ p2) ∧ p4) ∧ p4))))) ∧ p4) ∨ (False → (p4 ∧ False))) := by
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
theorem thm_5_vars_247366179866036918614497560566 : ((False ∨ p1) ∨ ((((True ∧ (((p4 ∧ p4) ∧ False) ∨ (p1 → p3))) ∨ (False ∧ (False ∨ p4))) ∨ True) ∨ ((p1 ∧ p4) → ((True ∨ p5) → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173002672831003551007970062605 : ((p5 ∧ ((p1 → (p4 ∨ p3)) → ((p3 ∧ (True → p3)) ∧ ((p2 ∧ p1) ∧ False)))) ∨ ((p4 ∨ (False ∧ p2)) ∨ (((p3 ∨ False) ∨ True) ∨ p4))) := by
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
theorem thm_5_vars_135140873228650387638327890040 : (((p2 ∨ ((p3 → ((p5 ∨ (p1 ∧ ((p3 ∨ p4) → ((True → p1) ∨ (p1 ∧ p3))))) ∧ True)) ∧ p1)) ∨ (p1 ∨ p1)) ∨ (False → (True ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61953403256615221774099995969 : ((p2 ∧ (((p1 ∨ (p4 ∨ ((p3 → p2) ∧ (((True → p5) ∨ p3) ∨ p4)))) → p3) ∨ ((p4 ∨ (False ∧ (p5 ∧ p1))) ∨ (True → True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187214232247828088557548223224 : (((False → True) → (((False → (p5 ∧ p5)) ∨ (p2 ∨ p1)) ∧ False)) → (((p2 ∨ p1) → (p2 → (((True → p1) → True) → (p1 ∧ p1)))) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245479793194833602542302467932 : ((p2 ∧ p5) ∨ (((p4 → ((False ∧ p2) ∨ False)) ∨ (((((p1 ∨ p2) ∨ p1) → (False ∧ (p1 ∨ True))) ∧ p3) ∨ p2)) ∨ ((p1 → p1) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785991785312583264352573637617 : (((p4 ∨ ((True ∧ (((((((True → (p4 ∨ p4)) ∧ (p2 → (p1 → False))) → True) → p1) ∨ p1) → (p2 ∨ True)) → p1)) ∨ (True ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68026630615343969718066454005 : ((p2 → (p1 ∧ ((p1 → (((p1 ∧ ((p3 ∨ p1) ∧ (p1 ∨ (False ∨ True)))) → ((p5 → (p4 ∧ p3)) ∨ (p4 ∨ p3))) → p1)) → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_664535153253321607339871131133 : ((((p5 ∨ ((((p1 ∧ (p1 ∨ (False → (p1 ∧ (True ∧ p3))))) ∨ p1) → (True ∨ (((p3 ∧ p1) ∨ p1) ∨ p3))) → p3)) → (p4 → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111886799316369172999245487629 : ((((((p3 ∨ (p4 ∧ (p3 → (False ∧ p3)))) ∧ True) ∨ (True ∨ (p4 ∨ p3))) ∧ (p5 ∨ ((p5 ∨ (True ∨ False)) ∨ p3))) ∨ p2) ∨ (False ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_191798757731262011694971642560 : ((p2 ∨ ((((p4 ∧ False) → (True ∧ False)) ∨ p3) → False)) ∨ (((p2 ∧ p3) ∧ ((p4 ∧ (p2 ∨ p1)) → ((p2 → p1) → (p1 → p1)))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_496405716099059498332998901595 : (((((p4 ∧ p5) ∨ True) ∧ ((False ∨ (p5 ∨ p2)) ∨ (((((True ∨ (False → (True ∨ p4))) ∧ True) ∨ ((p1 ∧ False) ∧ False)) ∨ p4) ∨ False))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173320370038602133746139011366 : ((p2 → ((p2 → ((((p4 ∧ p2) ∧ False) ∧ ((p2 ∨ p5) → p3)) ∧ p2)) ∨ p1)) ∨ ((p2 ∨ ((True → p4) → False)) ∨ (p2 → (p2 ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112016945508193396236590784990 : (((((True ∧ p3) ∨ False) ∧ (((p4 ∨ p1) ∨ (True ∨ ((p1 ∨ ((p4 ∧ (False ∨ False)) → False)) ∧ (p1 ∧ p3)))) ∧ p3)) ∨ True) ∨ (p4 ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213450996525310722105514517378 : (((p5 ∨ (p1 → p2)) ∧ False) ∨ ((((True ∨ ((p2 ∧ (((True ∨ (p3 → (p4 ∧ True))) → p1) ∧ True)) ∨ (p3 ∨ p5))) ∨ p2) → p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116470407093318598910798043266 : (((False ∧ p5) ∧ ((p1 ∧ (False ∧ True)) ∨ ((p3 ∧ (p5 → ((True ∨ (True → p3)) ∧ (True → p5)))) ∨ (p5 ∧ (True ∨ p5))))) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788293742571011329247339589824 : (((p5 ∨ (((((p5 ∧ p2) ∧ (p2 ∨ (p4 → ((p1 ∧ (((p3 ∧ p1) ∧ p5) ∨ True)) ∧ p2)))) ∨ (False ∧ (p2 ∧ False))) ∧ p2) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38130848603929881266553179842 : ((((((False ∨ p1) ∧ p5) → (False ∨ ((((p3 ∧ False) ∧ False) → p1) → ((p2 → p4) ∨ (p4 ∨ p3))))) ∧ ((p2 ∧ p4) → p5)) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749409786108011226720545546565 : (((True ∧ ((((p1 ∨ ((False ∨ (p1 ∨ (p1 ∧ (((True ∧ True) ∨ (False ∧ (p3 → True))) ∧ True)))) → p4)) → p1) ∨ (p3 ∧ p2)) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_899117934830965087388428055652 : ((((((False ∨ p2) ∨ ((((False ∨ (p5 ∨ (p2 ∨ p1))) ∨ (p2 → (True → p2))) ∨ p2) ∨ p2)) ∧ (p2 ∨ True)) → (p1 ∧ (True ∧ p5))) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((False ∨ p2) ∨ ((((False ∨ (p5 ∨ (p2 ∨ p1))) ∨ (p2 → (True → p2))) ∨ p2) ∨ p2)) ∧ (p2 ∨ True)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40367034988975674328755435444 : ((((((p4 → p1) → ((p5 ∨ ((((p1 ∨ (True → (p5 ∧ (False ∧ (True ∧ p3))))) ∧ p4) → p3) ∧ p4)) ∨ p4)) → p5) ∨ False) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301242323508608435481846718134 : (False ∨ ((((False → (p5 ∧ True)) → p1) ∨ p5) ∨ (((p2 ∧ (p4 ∧ (p4 ∧ p2))) ∧ p1) ∨ ((((p3 ∨ p3) ∧ (False → p3)) ∨ p3) ∨ True)))) := by
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
theorem thm_5_vars_339508386048612312147268996927 : (p1 → (False ∨ ((True ∨ (((False → p3) ∨ p5) → p4)) → ((p5 ∧ (p5 ∧ (p2 ∨ (p1 ∧ (True → (p1 ∧ p2)))))) → (p4 ∨ (p2 ∧ p2)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h8
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h8
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h14 =>
      -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
      have h15 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h13, we can now drive its conclusion.
      let h16 := h13 h15
      -- We need to get the right conjuct of h16 based on <expert-advice>.
      let h17 := h16.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h17
      -- One of the premise coincides with the conclusion.
      exact h17
    case inr h18 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
      have h19 : ((False → p3) ∨ p5) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h18, we can now drive its conclusion.
      let h20 := h18 h19
      -- One of the premise coincides with the conclusion.
      exact h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247918683152477924521873628984 : ((p1 ∨ p3) ∨ ((((False → p5) → ((p1 ∧ False) ∧ p5)) → p2) → (((p2 ∨ ((p4 ∧ False) ∨ (p3 ∨ p4))) → (False ∨ (True ∧ p3))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43864737653676815043074039022 : ((((((True → (p1 ∧ (False ∧ p2))) ∧ p2) ∧ ((p4 → ((False → p2) ∨ p3)) → (p2 ∨ (p3 → (False ∨ True))))) ∧ (p4 ∧ p1)) → p2) ∨ False) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h3.left
  let h9 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173132947551490535703923940177 : ((p2 ∨ (p2 → ((p1 ∧ (p1 ∧ (p3 ∨ (p3 ∨ (p3 ∧ p5))))) ∧ (p5 ∨ p1)))) ∨ (p2 → (((p5 ∧ p3) → (False → p4)) ∧ (True → p2)))) := by
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
  apply False.elim h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351003921445989004280658984145 : (p4 → ((p2 ∨ (((p3 ∨ (p2 → ((p5 → (p1 ∨ (p3 ∧ False))) ∨ False))) → (p1 ∧ (p5 → ((True → p2) → p1)))) ∨ p5)) ∨ (p5 ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216885625014066675780643548325 : (((p2 ∨ (False ∨ p4)) ∧ p2) → ((p1 ∨ p1) ∨ ((p5 ∨ (p5 → (True ∨ (False → p1)))) ∨ (False ∨ (((p4 → p1) ∨ p1) ∨ (p4 ∨ p5)))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49996004405668435940165045013 : ((((p3 ∧ ((True → p4) ∨ ((False ∨ p2) → (p5 ∨ p3)))) ∨ ((p3 → p3) ∧ ((p3 ∧ p3) ∧ p2))) ∧ (p3 ∧ ((p3 → p4) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299787631653808919432647538337 : (False ∨ (((True → False) ∧ (((((p4 ∨ (True → (True → p1))) ∧ (p3 ∨ False)) → (True ∨ (p2 → p2))) ∨ p3) ∨ (p5 ∨ (p4 ∨ True)))) → p4)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h6 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h7 := h2 h6
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h9 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h10 := h2 h9
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h13 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h14 := h2 h13
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- One of the premise coincides with the conclusion.
        exact h16
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
theorem thm_5_vars_217138502939526206050726315213 : ((((p1 → True) ∨ p3) ∨ p1) → (((False ∨ (((False ∨ p3) → p3) ∧ p4)) ∨ True) ∨ ((p5 ∧ (p4 ∨ False)) ∧ (False ∧ ((p1 ∧ p3) ∨ p2))))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113973930290188388297658459355 : (((p4 ∧ (p5 ∨ (p2 ∨ (False → (((((p4 → p2) ∧ False) ∨ False) → (p2 ∨ (True ∨ p4))) ∧ False))))) ∧ (p3 ∨ (p4 ∧ p5))) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232963283578911704151789430697 : ((p3 ∧ (True → p1)) → ((p3 ∨ p3) → ((p2 → (p4 ∨ (p5 ∨ p5))) ∨ (p3 ∧ (p3 → (((((False ∨ p3) ∨ p5) ∨ True) ∧ p1) → p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h1.left
    let h5 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h4
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- False on the left can always be used.
          apply False.elim h12
        case inr h13 =>
          -- One of the premise coincides with the conclusion.
          exact h9
      case inr h14 =>
        -- One of the premise coincides with the conclusion.
        exact h9
    case inr h15 =>
      -- One of the premise coincides with the conclusion.
      exact h9
  case inr h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h1.left
    let h18 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h17
    -- Implications on the right can always be decomposed.
    intro h19
    -- Implications on the right can always be decomposed.
    intro h20
    -- Conjunctions on the left can always be decomposed.
    let h21 := h20.left
    let h22 := h20.right
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h23 =>
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h24 =>
        -- Disjunctions on the left can always be decomposed.
        cases h24
        case inl h25 =>
          -- False on the left can always be used.
          apply False.elim h25
        case inr h26 =>
          -- One of the premise coincides with the conclusion.
          exact h22
      case inr h27 =>
        -- One of the premise coincides with the conclusion.
        exact h22
    case inr h28 =>
      -- One of the premise coincides with the conclusion.
      exact h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254346032055988432699296923330 : ((p2 ∧ p4) → (((((p5 → p3) ∨ ((False → False) ∧ False)) ∧ (p1 ∨ ((p3 → (p4 ∧ p1)) ∨ (p2 → False)))) → False) ∨ ((False ∧ p3) → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147903882068928646457039015633 : (((((((p3 ∧ (p4 ∨ p4)) → p2) → (p5 ∧ (False → p3))) → ((p2 ∨ False) ∨ p5)) → p5) ∧ (True ∨ True)) ∨ ((p4 → p4) → (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340827557343758270581623391311 : (p2 → (((p5 ∨ ((True → (((p2 → (p2 → p2)) ∧ p1) ∨ p2)) → (p3 → ((p2 → (False ∧ p1)) ∧ (p1 → p3))))) ∨ (True ∨ p3)) ∨ p5)) := by
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
theorem thm_5_vars_148610366436341781042135904196 : (((((((p5 ∧ p2) ∧ p3) ∧ p3) ∨ (False ∨ True)) ∨ p4) → (((p5 ∧ (p4 → (p3 ∧ True))) ∧ True) ∧ False)) ∨ (((p3 ∧ p5) → True) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221107674479102511858569330379 : (((p5 ∧ p5) ∨ True) ∧ ((((p4 ∨ (((False → p5) ∨ (p1 ∧ p2)) → True)) ∨ (False ∧ ((p5 ∧ True) ∧ (p2 ∨ p2)))) → (p3 → p1)) ∨ True)) := by
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



