variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116288585596769189434551103376 : (((p3 ∨ (p2 ∨ p3)) ∨ ((True ∨ ((p5 → ((p5 ∨ p2) ∨ False)) ∧ p3)) → ((p5 ∧ p1) ∧ (p5 → (p2 ∨ (True ∧ p2)))))) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193235151703134096475009664571 : ((((p1 → p2) ∨ p1) ∧ ((p2 ∨ p1) ∨ (p5 ∨ p3))) → ((p4 ∧ True) ∨ (p4 → ((p1 ∧ ((False → (p2 → False)) → (p3 ∧ p5))) → p3)))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h7
        -- Implications on the right can always be decomposed.
        intro h8
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
        have h11 : (False → (p2 → False)) := by
          -- Implications on the right can always be decomposed.
          intro h12
          -- Implications on the right can always be decomposed.
          intro h13
          -- False on the left can always be used.
          apply False.elim h12
        -- We have shown the premise of h10, we can now drive its conclusion.
        let h14 := h10 h11
        -- We need to get the left conjuct of h14 based on <expert-advice>.
        let h15 := h14.left
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h17
        -- Implications on the right can always be decomposed.
        intro h18
        -- Conjunctions on the left can always be decomposed.
        let h19 := h18.left
        let h20 := h18.right
        -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
        have h21 : (False → (p2 → False)) := by
          -- Implications on the right can always be decomposed.
          intro h22
          -- Implications on the right can always be decomposed.
          intro h23
          -- False on the left can always be used.
          apply False.elim h22
        -- We have shown the premise of h20, we can now drive its conclusion.
        let h24 := h20 h21
        -- We need to get the left conjuct of h24 based on <expert-advice>.
        let h25 := h24.left
        -- One of the premise coincides with the conclusion.
        exact h25
    case inr h26 =>
      -- Disjunctions on the left can always be decomposed.
      cases h26
      case inl h27 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h28
        -- Implications on the right can always be decomposed.
        intro h29
        -- Conjunctions on the left can always be decomposed.
        let h30 := h29.left
        let h31 := h29.right
        -- We want to use the implication h31 based on <expert-advice>. So we show its premise.
        have h32 : (False → (p2 → False)) := by
          -- Implications on the right can always be decomposed.
          intro h33
          -- Implications on the right can always be decomposed.
          intro h34
          -- False on the left can always be used.
          apply False.elim h33
        -- We have shown the premise of h31, we can now drive its conclusion.
        let h35 := h31 h32
        -- We need to get the left conjuct of h35 based on <expert-advice>.
        let h36 := h35.left
        -- One of the premise coincides with the conclusion.
        exact h36
      case inr h37 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h38
        -- Implications on the right can always be decomposed.
        intro h39
        -- Conjunctions on the left can always be decomposed.
        let h40 := h39.left
        let h41 := h39.right
        -- One of the premise coincides with the conclusion.
        exact h37
  case inr h42 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h43 =>
      -- Disjunctions on the left can always be decomposed.
      cases h43
      case inl h44 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h45
        -- Implications on the right can always be decomposed.
        intro h46
        -- Conjunctions on the left can always be decomposed.
        let h47 := h46.left
        let h48 := h46.right
        -- We want to use the implication h48 based on <expert-advice>. So we show its premise.
        have h49 : (False → (p2 → False)) := by
          -- Implications on the right can always be decomposed.
          intro h50
          -- Implications on the right can always be decomposed.
          intro h51
          -- False on the left can always be used.
          apply False.elim h50
        -- We have shown the premise of h48, we can now drive its conclusion.
        let h52 := h48 h49
        -- We need to get the left conjuct of h52 based on <expert-advice>.
        let h53 := h52.left
        -- One of the premise coincides with the conclusion.
        exact h53
      case inr h54 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h55
        -- Implications on the right can always be decomposed.
        intro h56
        -- Conjunctions on the left can always be decomposed.
        let h57 := h56.left
        let h58 := h56.right
        -- We want to use the implication h58 based on <expert-advice>. So we show its premise.
        have h59 : (False → (p2 → False)) := by
          -- Implications on the right can always be decomposed.
          intro h60
          -- Implications on the right can always be decomposed.
          intro h61
          -- False on the left can always be used.
          apply False.elim h60
        -- We have shown the premise of h58, we can now drive its conclusion.
        let h62 := h58 h59
        -- We need to get the left conjuct of h62 based on <expert-advice>.
        let h63 := h62.left
        -- One of the premise coincides with the conclusion.
        exact h63
    case inr h64 =>
      -- Disjunctions on the left can always be decomposed.
      cases h64
      case inl h65 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h66
        -- Implications on the right can always be decomposed.
        intro h67
        -- Conjunctions on the left can always be decomposed.
        let h68 := h67.left
        let h69 := h67.right
        -- We want to use the implication h69 based on <expert-advice>. So we show its premise.
        have h70 : (False → (p2 → False)) := by
          -- Implications on the right can always be decomposed.
          intro h71
          -- Implications on the right can always be decomposed.
          intro h72
          -- False on the left can always be used.
          apply False.elim h71
        -- We have shown the premise of h69, we can now drive its conclusion.
        let h73 := h69 h70
        -- We need to get the left conjuct of h73 based on <expert-advice>.
        let h74 := h73.left
        -- One of the premise coincides with the conclusion.
        exact h74
      case inr h75 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h76
        -- Implications on the right can always be decomposed.
        intro h77
        -- Conjunctions on the left can always be decomposed.
        let h78 := h77.left
        let h79 := h77.right
        -- One of the premise coincides with the conclusion.
        exact h75



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56171402220460411205974300064 : (((p1 ∧ (True → (False → False))) ∨ (p5 → ((p3 ∨ ((p1 ∧ True) → p5)) → (p4 ∨ (p3 ∨ (p4 → (p2 ∨ (p4 ∧ (p4 → p4))))))))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257481168414279263135775378558 : ((p3 ∨ True) → (p5 → (p2 ∨ ((((p4 ∧ (p5 → True)) → False) ∧ p2) ∨ (((p1 ∨ p3) → ((p2 ∨ p1) ∨ (p2 ∨ (False → p4)))) ∧ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- False on the left can always be used.
      apply False.elim h7
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h9
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- False on the left can always be used.
      apply False.elim h12
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61197268791105508060101783681 : ((False ∧ ((p5 ∨ p3) ∨ (p1 → ((((((((p4 ∧ p4) ∧ p2) → ((p1 → p2) → p3)) ∧ p3) → p3) ∧ (p2 ∧ True)) ∧ p1) ∧ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_667423282338843376531109540504 : (((((p4 ∨ p1) → (p4 → (p2 → (p3 ∨ (((True → True) → p4) → ((False ∨ (p2 ∨ False)) → (False ∨ False))))))) ∧ (p5 ∨ (p1 ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313104084033992838073615333429 : (p3 ∨ ((((((True ∨ p4) ∧ (True → (False ∧ ((p4 → False) → p2)))) ∧ False) ∨ ((True ∨ False) ∧ (p5 ∨ p1))) ∧ (p3 ∨ (p4 ∨ p5))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147264277573991023984745054286 : (((((p1 ∧ (((p2 ∧ p2) → (((False ∧ p5) ∨ (p4 ∨ p2)) ∧ p3)) ∧ (p3 ∧ True))) ∨ p2) ∨ True) ∨ p1) ∨ (False ∨ (p3 → (p3 → p4)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61026509203923175462757772936 : ((False ∧ (((True ∧ (((False ∨ ((p5 ∨ p1) ∨ ((True → p2) ∨ True))) ∧ p2) ∨ ((p2 → p5) ∧ p4))) ∧ (p1 ∧ True)) ∧ (True → True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313921656740506155113411574325 : (p3 ∨ ((((p4 → (False → (((p2 ∧ False) → (True ∨ True)) ∨ (p3 → (False → ((p1 → p1) ∧ (p1 ∨ p3))))))) → p1) ∧ p1) ∨ (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37984667940853258935929588732 : (((((p2 → (True ∨ ((p5 ∨ True) → ((p3 → (p3 ∧ p2)) ∧ p3)))) ∧ (p3 ∧ ((p1 ∨ p2) ∨ (p5 ∨ False)))) ∨ (False → p1)) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47132582393497412936181414427 : ((((p4 ∨ ((p4 → p5) ∧ (p2 ∨ (False → (p2 → (p1 → (((p3 ∧ True) ∨ p3) ∧ p5))))))) → ((False ∨ p5) ∨ True)) ∨ (False → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_18050382625495157309307671778 : (((p1 ∧ ((((False ∧ p1) ∨ (p4 ∧ (((True ∨ True) ∧ (p3 ∧ (p4 ∧ True))) ∧ p1))) ∨ p4) ∨ p1)) ∨ (((False ∨ True) → p5) → p5)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258947634704698790404596730384 : ((True → p3) → (((True → ((p2 ∨ p2) ∧ p5)) ∧ (((p1 ∨ False) ∨ p3) ∧ (True ∧ (((p1 → p1) ∨ (p3 ∧ (p1 → False))) → p5)))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165446856702175632075874421041 : (((((p3 ∧ ((p5 ∨ p5) ∧ (p2 ∧ True))) ∨ True) ∨ p1) ∧ ((p1 ∧ (True ∧ p4)) ∨ True)) ∨ ((p4 ∨ p5) ∨ (True ∧ ((p1 ∧ p4) ∨ p1)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111690716716628863304139347090 : (((((False → ((p3 ∨ (p3 ∨ (True ∨ ((p2 → False) ∧ (((p2 ∨ p5) ∧ False) → p4))))) ∧ (True ∧ True))) ∨ p2) → p3) ∨ p5) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114626941421609190142597842546 : ((((((p1 ∨ (p5 → ((p1 ∨ (p3 ∧ p3)) ∨ p3))) ∨ (False → False)) ∨ p3) ∨ p4) ∨ (p4 ∧ ((False → True) → (p1 ∨ p3)))) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157020111924586915096167730725 : ((((p1 ∨ p2) ∧ (p2 → ((p5 ∨ p4) ∨ ((((p1 ∨ p2) ∨ (p4 ∨ p5)) ∨ True) ∧ p2)))) ∨ p4) ∨ ((p4 → ((False ∧ False) → True)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41811785487711608999326846653 : (((((p1 ∨ p1) ∧ True) ∧ (p1 ∧ (p1 ∧ ((((((p5 ∧ (p2 ∧ (True → p5))) ∧ True) ∨ p2) → p4) → True) → (p2 → p2))))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136829643905693501663647473009 : (((False ∧ p3) ∨ ((False ∨ p1) → (((p1 ∨ p2) ∧ ((p2 ∨ True) ∨ (p5 → (p5 ∧ ((True → p4) ∨ p5))))) → p3))) ∨ (p1 → (p2 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249913221660767482814718887205 : ((True → p1) ∨ ((p1 ∧ (p2 ∧ ((((((p2 ∧ True) ∧ p1) ∧ True) ∨ True) → False) ∨ ((False ∧ (False → p5)) → p5)))) ∨ (p4 ∨ (False → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_752044358487520799441480065963 : (((True ∧ (True → ((p3 ∨ (p4 ∧ ((p2 ∧ True) ∨ (p3 ∧ p4)))) ∨ (((p5 ∨ (p4 ∨ (p2 → False))) ∧ False) → ((p4 → False) → p4))))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_724478152275865523620396793208 : ((((True ∨ (p5 → True)) ∧ (p3 ∨ (p5 → ((p1 ∨ p2) ∧ ((False ∧ (p5 ∧ p5)) ∨ ((True → True) → ((False ∧ (p4 → p1)) ∨ p1))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250885236771575640774445433732 : ((p1 → p3) ∨ ((((p1 → ((((p3 ∨ p4) → ((p2 ∧ p2) ∧ p2)) ∨ False) → False)) ∨ ((p2 → p4) → p3)) ∨ p2) → ((True → False) → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h5 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h6 := h2 h5
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h8 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h9 := h2 h8
      -- False on the left can always be used.
      apply False.elim h9
  case inr h10 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h11 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h12 := h2 h11
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66086998450561163511089933426 : ((p5 ∨ ((((((p1 ∨ True) → p2) ∧ ((True ∨ p4) ∧ p3)) ∨ (((p3 ∨ p5) → p1) ∧ (True → ((False → p4) ∨ p1)))) ∧ True) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299216850921409641088898119783 : (False ∨ ((((p2 ∨ (True ∨ p3)) ∧ (((p5 → (p3 ∨ p4)) ∧ (((p1 ∨ p1) → p2) ∨ ((False ∨ p4) → p3))) ∨ p5)) ∨ (True ∧ p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232389537521967996837056170204 : (((p5 → p2) → p1) → ((((False → True) → ((((True → False) ∧ True) → True) → True)) → p3) ∨ (((p1 → ((p2 ∧ p4) ∨ p1)) ∨ False) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342612147906024558771296222159 : (p2 → ((p4 ∧ (((p3 ∨ (p3 → (p2 → p3))) ∨ p5) → (p2 ∨ p3))) → (((p4 → ((p5 ∧ p1) ∨ (p3 ∧ p3))) ∧ (p1 → p2)) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114347264931061657204843447545 : (((True → (((p2 ∧ (p2 ∧ p2)) ∨ ((((p2 ∧ False) ∧ p3) ∧ False) ∨ False)) ∧ (p5 → p5))) ∧ ((p4 → (False ∨ p1)) → p4)) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229123176262936294651434516502 : ((True → (p2 ∧ p2)) ∨ (((((((p4 ∧ (p5 ∧ (p3 ∨ (p1 → (p4 ∧ p4))))) → p5) ∨ (p4 ∨ False)) → p2) → p3) ∨ True) ∨ (p1 ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179855440853810661888194561627 : (((p5 ∨ (p5 ∧ (((p2 ∧ True) ∧ (p5 → (False → p5))) ∧ True))) ∧ p5) → ((p1 ∧ (((False ∧ (True ∨ p5)) ∨ p3) ∨ p3)) ∨ (False → p3))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h11.left
    let h14 := h11.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h15
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258762120835233805990370224883 : ((True → False) → ((p4 → (((p5 ∨ p2) ∨ (False → p5)) → ((p4 ∧ True) ∧ (((p4 → p1) ∧ p5) ∧ (p2 ∧ (p2 ∨ (True ∧ p3))))))) ∧ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h6 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h8
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h11 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h12 := h1 h11
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h14 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h15 := h1 h14
      -- False on the left can always be used.
      apply False.elim h15
  case inr h16 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h17 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h18 := h1 h17
    -- False on the left can always be used.
    apply False.elim h18
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h19 =>
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- One of the premise coincides with the conclusion.
      exact h20
    case inr h21 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h22 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h23 := h1 h22
      -- False on the left can always be used.
      apply False.elim h23
  case inr h24 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h25 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h26 := h1 h25
    -- False on the left can always be used.
    apply False.elim h26
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h27 =>
    -- Disjunctions on the left can always be decomposed.
    cases h27
    case inl h28 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h29 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h30 := h1 h29
      -- False on the left can always be used.
      apply False.elim h30
    case inr h31 =>
      -- One of the premise coincides with the conclusion.
      exact h31
  case inr h32 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h33 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h34 := h1 h33
    -- False on the left can always be used.
    apply False.elim h34
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h35 =>
    -- Disjunctions on the left can always be decomposed.
    cases h35
    case inl h36 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h37 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h38 := h1 h37
      -- False on the left can always be used.
      apply False.elim h38
    case inr h39 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h39
  case inr h40 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h41 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h42 := h1 h41
    -- False on the left can always be used.
    apply False.elim h42
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h43 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h44 := h1 h43
  -- False on the left can always be used.
  apply False.elim h44



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137919078487728472745290520470 : ((p4 ∨ ((p1 ∨ p1) ∨ (((p2 → p5) ∨ (p2 ∧ p1)) ∨ (p3 → ((False ∨ ((False → True) ∨ (True ∧ p5))) ∨ p1))))) ∨ ((True ∧ p5) ∨ p2)) := by
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
theorem thm_5_vars_207577994522816218121373765040 : ((((p1 ∨ (False ∨ False)) ∨ p4) → p2) → (p4 ∨ ((p3 → (p5 ∨ (((((p1 ∨ p5) ∨ True) → p5) → p4) ∨ p3))) ∨ (False ∧ (p1 ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304736935696538260193180409111 : (p1 ∨ ((((p3 → (True ∨ (p5 ∧ p3))) ∧ p2) ∨ ((p5 ∧ ((False ∨ (False ∧ ((p3 ∨ p4) → (p3 → True)))) ∧ p5)) ∨ p5)) ∨ (p2 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38262933352464345280151643198 : ((((True → (((((p1 ∧ p4) → ((p3 → False) → (p2 → p2))) ∧ (p4 ∧ p3)) ∨ p4) ∧ False)) ∧ ((False ∨ (True ∨ False)) ∨ p1)) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58210320413157535085009872934 : (((p4 ∧ p1) ∧ ((((p3 → False) → p5) → ((p4 ∨ True) ∧ (False ∨ (True → (((True ∧ p4) ∧ True) → p5))))) ∧ ((p1 ∨ True) ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51244156730448042940684229751 : (((((False → p2) ∧ p3) → ((((p1 → (p3 ∧ p2)) ∨ p5) ∨ p4) ∧ (False ∧ (False ∧ p4)))) ∨ (((p1 ∧ (p2 ∧ p3)) ∧ True) ∨ True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249691681707034835469183700108 : ((p5 ∨ p4) ∨ (True ∧ (False ∨ (((False ∨ p1) → (True → False)) ∨ (((p3 ∨ (False → p4)) ∨ ((False → p2) ∧ p5)) ∨ (p1 ∧ (p3 → p5))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_728162050937150163770358103685 : ((((p5 ∨ (True → p5)) ∨ ((p3 ∨ (((((True ∨ (p4 ∧ p1)) → (p5 ∧ p4)) ∧ (p2 → False)) ∨ (p4 → True)) ∧ (False → p1))) ∨ p3)) ∨ p3) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159026108695601260127726451614 : ((p4 ∨ ((p1 ∨ p1) ∧ ((((((p3 → p3) ∨ p5) → False) ∧ (p3 ∨ p2)) → True) → (p2 → p4)))) ∨ ((p3 ∨ ((p1 ∨ p2) ∨ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118191584994529673057243885961 : ((False ∨ (p3 ∨ (p4 ∧ (((p5 → (((True ∧ (p1 → p2)) → p5) ∨ True)) → False) ∨ ((p3 ∧ (True ∧ p4)) → (p1 ∨ False)))))) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197996771529152038464570229970 : (((True → True) ∧ ((p1 ∨ (True ∧ p4)) ∧ p1)) ∨ ((p2 ∧ p5) ∨ ((p4 → True) ∨ ((((p5 → True) → True) → p5) ∧ ((p2 ∨ p3) ∨ p1))))) := by
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
theorem thm_5_vars_750265928427595478167231974795 : (((True ∧ ((((True ∧ ((p3 ∧ (True → p4)) ∨ p3)) → p2) ∧ (p5 ∧ ((p5 ∧ ((p5 ∧ (p2 ∧ p3)) ∨ False)) ∨ p4))) ∨ (True → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187835885085631907826692694021 : ((p5 → ((True ∨ ((p1 ∨ True) → ((p4 → True) ∧ p4))) ∧ False)) → ((p5 → (True → (p4 ∧ (p4 ∨ p3)))) ∨ (True → (p5 ∨ (p1 ∧ p2))))) := by
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h7
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354643582425227844864467656968 : (p5 → ((((p2 → ((((p2 → False) ∧ p3) ∨ p1) ∨ (((p3 ∨ p1) → (p3 ∧ (((p5 ∧ p5) → p2) ∨ p2))) → p4))) ∨ p1) → p3) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_96970172122132262565537216860 : ((p1 ∨ ((p5 ∨ True) → (p4 ∧ (((False → (((((p5 ∨ p5) → (p3 ∧ (p5 ∧ p5))) ∧ (p4 → p2)) → False) ∨ p1)) ∨ p2) ∧ False)))) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : (p5 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- We need to get the right conjuct of h5 based on <expert-advice>.
    let h6 := h5.right
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113102975347919449114577701286 : (((True → ((p4 ∧ (((p1 → (True ∧ (p1 ∧ (p4 ∧ p2)))) → p2) ∨ ((False ∧ False) ∧ True))) → ((p5 → p2) ∨ p4))) → p2) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2921701782039281093977181036 : ((p5 → (p5 ∧ p5)) ∧ (((p3 ∧ p5) ∨ p3) → ((False ∨ (False ∨ (p1 ∧ False))) ∨ (False ∨ ((p1 ∨ (p3 ∧ True)) ∧ (True ∨ True)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h4
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h6
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147813755652297685065669729436 : (((p4 ∧ ((True ∨ False) ∨ ((False → (p1 ∨ p5)) ∧ (p5 → (p4 ∧ (((p5 ∧ p2) ∨ p3) → True)))))) → p3) ∨ ((p5 ∧ False) → (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115063717376194660749399846783 : (((((p2 ∧ p5) ∨ (p5 → p2)) ∧ (p3 ∨ ((p5 ∧ p4) ∨ p3))) ∨ (True ∧ (False → ((p5 → p4) ∨ (p4 ∧ (p3 → True)))))) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40198070860313190901949905392 : (((((p4 → (p1 ∧ p2)) → (((p1 ∧ (p1 ∨ ((False ∨ p2) ∧ p5))) → (True ∨ p1)) ∧ (p2 ∧ ((p4 → p3) ∧ p2)))) ∧ True) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159235370549729344047203546205 : ((p3 → (((((p3 → p3) ∧ (True ∧ (p2 ∨ p4))) ∨ p1) ∨ (True ∨ ((p3 ∧ False) ∧ p1))) → p1)) ∨ ((((p4 → p4) ∨ p3) ∧ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_805529928512759355581584528368 : (((p3 → (p4 ∨ ((p4 → (False → ((p3 ∧ p1) ∧ False))) ∧ (True ∧ (((True → (p5 ∨ (p5 ∨ True))) → (False ∧ (False ∨ p3))) ∨ p3))))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h3
  -- False on the left can always be used.
  apply False.elim h3
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315716356782896977306290529924 : (p3 ∨ ((True → False) ∨ (((p4 → p2) → ((((p1 → p2) → p3) → (((p3 ∨ True) ∧ (p2 ∧ ((False ∨ True) ∧ False))) ∧ p2)) ∨ True)) ∨ p5))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_210263004140422721556367042226 : ((((p5 ∨ p3) → True) ∨ p1) ∧ (((True ∨ p5) ∧ p5) → ((p1 ∧ (p2 ∨ False)) ∨ ((p1 ∨ (True → (p2 ∨ p1))) ∨ ((p4 ∨ p3) ∨ True))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316698516536712199718567756589 : (p3 ∨ (p5 ∨ (((False → True) ∨ (p1 ∧ p4)) → (((False ∧ (((True ∨ True) → p3) ∨ (p5 ∨ (True → p2)))) ∨ p4) ∨ (True → (False → p4)))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199564161377916686912231794518 : ((((((p4 ∨ False) → True) → p4) ∨ p2) → p4) → (True ∧ ((((p3 ∨ (True ∧ (p4 ∨ True))) ∨ (p2 → False)) → p2) → ((False ∧ p3) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((p3 ∨ (True ∧ (p4 ∨ True))) ∨ (p2 → False)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66169450628975904427741515089 : ((p5 ∨ ((True → ((((False ∧ p4) ∨ p1) ∨ p2) ∧ (p4 ∧ ((p5 → ((p3 ∨ p3) ∧ p3)) ∨ (p3 ∨ p2))))) ∨ ((False ∨ True) ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_643033113065845451155332664580 : ((((p2 ∧ (p4 ∧ (((p1 ∨ ((p3 → p3) → ((p4 ∨ p3) ∨ p4))) ∧ (p4 → ((p4 → (True ∧ True)) ∧ (p2 → p3)))) ∧ p4))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205664368855257859154893053417 : (((p1 ∨ p1) ∨ (p4 ∧ (p2 ∧ p5))) ∨ ((p4 ∨ (p5 → (((((p1 → True) ∨ (p2 ∨ False)) → (p3 → (False ∨ True))) ∧ False) → p5))) ∨ p4)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249167584248009289902679096427 : ((p4 ∨ p3) ∨ ((((((p3 ∧ (p2 ∧ False)) ∧ (((p1 ∨ True) → p5) ∨ p2)) → (p4 ∨ ((p2 ∨ (p5 → p3)) ∧ p1))) → p2) ∨ True) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177755943323549339756759487946 : ((((p1 ∨ False) ∨ (p2 → (p1 → (p5 → (False ∨ (p5 → False)))))) ∧ p4) ∨ (((p5 ∨ False) ∧ ((((p5 ∧ p3) → p1) ∧ p1) ∨ False)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_266034998609005650185748761867 : (True ∧ (p1 → (True ∧ ((((((p4 → p4) ∧ False) ∧ False) ∧ (False → (True → False))) ∧ (p2 → ((p5 ∧ (p3 ∧ p2)) ∨ (p1 ∧ p4)))) ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_184385103822209373161185999641 : (((p1 → (p3 → (False ∨ ((True → True) ∧ (p1 ∨ p3))))) → p5) ∨ (p5 → (((p3 → (p4 → p1)) ∧ True) ∨ (p2 ∨ ((p5 ∧ False) → False))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69254934044691488426063661350 : ((p5 → ((p5 ∨ (p1 ∧ p2)) → ((p2 ∧ (((((p2 → p3) → p1) → p5) → p5) → p1)) ∨ (((p2 ∧ (p2 ∨ p1)) → False) ∨ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157358299765027533160716852761 : (((False → (p5 → ((p5 ∧ (True ∨ ((((True ∧ p4) ∧ False) → (False ∨ p4)) ∧ True))) ∧ p4))) → False) ∨ ((p3 ∧ p4) ∨ (False → (p3 ∧ True)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115817222300508117682550614189 : ((((p4 ∨ p1) ∧ (p3 ∧ False)) ∧ (((((p3 ∨ (p1 ∨ p1)) ∨ (p2 → p4)) ∧ (p4 ∨ ((p4 ∨ p3) ∨ p5))) → p4) ∧ p2)) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349416305043662696771947141533 : (p3 → (p4 → ((((False ∨ ((p2 ∧ False) ∧ False)) ∨ (((p4 ∨ False) → False) ∨ p5)) ∨ p3) ∨ (p1 ∧ (p2 → (True → ((True ∨ p5) ∨ False))))))) := by
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
theorem thm_5_vars_192988669006013349153652890828 : ((((p4 ∨ (p5 → (p3 ∧ p2))) ∧ True) → (p2 → p2)) → ((((False ∨ (True ∨ p3)) ∨ False) → (p3 ∧ p2)) → ((False ∧ (True → p5)) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((False ∨ (True ∨ p3)) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304790054410871050455472986837 : (p1 ∨ ((p5 → ((p2 → p4) ∨ ((False ∧ ((p3 → (p5 ∨ p5)) ∧ p1)) ∧ (False ∧ ((p5 ∧ (True ∨ p4)) ∧ (True → p1)))))) ∨ (True ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336444523325237455496091346595 : (p1 → ((p4 ∨ (p5 ∧ (((((p5 ∧ p2) → p4) → (p4 → ((True ∧ p3) ∨ True))) → (False ∧ p2)) → ((p3 ∧ (p1 ∨ p2)) ∨ False)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54342076436176869291182689451 : (((True ∨ (((p5 ∧ p5) → p4) ∨ (p1 ∨ p3))) ∧ (p4 ∨ ((((p2 → p3) ∨ ((False → p3) ∧ ((p5 ∧ True) ∧ p5))) ∨ p5) ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40482329470497145643431274836 : (((((p2 ∧ p3) ∨ (False ∧ (((p4 ∨ ((((p2 ∧ p5) ∧ (True ∨ ((p3 ∧ p1) → False))) → p1) → p3)) → p5) ∨ p2))) ∨ p1) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264405080375974612114124714501 : (True ∧ ((p3 ∧ ((p1 ∨ p4) ∨ p1)) ∨ (p2 ∨ (True → (True ∧ (p2 ∨ (p5 → ((p4 → True) ∧ ((((p2 ∨ p3) ∨ p3) → p5) ∨ p3))))))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184620637705243289732002044231 : ((((p4 → (p1 → True)) → (p2 → p4)) ∧ ((p1 ∨ p2) ∧ p4)) ∨ (((p5 ∨ p5) → ((True ∧ ((p4 → (p2 ∨ p5)) ∧ p1)) → p4)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149072154888253487841594014112 : ((((True → False) ∨ p4) → (p3 ∨ (((True → (False ∧ p2)) ∧ ((p3 ∧ p5) ∧ ((p2 → p3) ∨ p2))) ∧ p2))) ∨ (((p2 ∧ p4) → p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217396247526866503595368681095 : (((True → (False → p4)) ∨ True) → (True ∧ (((p1 ∨ (p4 → p5)) ∨ ((True → ((((p2 → p4) ∨ p3) ∧ p2) → (p4 ∨ True))) ∨ p4)) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
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
theorem thm_5_vars_2379180272082206486808504040 : ((False ∧ ((((p4 ∨ p2) ∨ (p3 ∧ (True ∧ p2))) → False) ∨ False)) ∨ (((p1 ∨ ((p4 → False) ∨ p2)) ∧ p1) → (p1 ∨ (p4 ∨ p2)))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
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
theorem thm_5_vars_48004320834742863298544421976 : (((((((True → ((p2 ∧ p5) ∨ p5)) ∨ False) ∨ ((p5 → p1) → p5)) → True) → ((True ∧ ((p1 → p1) → p1)) ∧ False)) → (p5 ∧ p5)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((True → ((p2 ∧ p5) ∨ p5)) ∨ False) ∨ ((p5 → p1) → p5)) → True) := by
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : ((((True → ((p2 ∧ p5) ∨ p5)) ∨ False) ∨ ((p5 → p1) → p5)) → True) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h6
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3230622331292036149150861305 : ((p2 ∨ False) ∨ (((p4 ∧ p2) ∧ p4) ∨ ((((p1 → (p4 ∧ (True ∧ p3))) ∨ (p1 ∨ p4)) ∨ ((p3 ∧ p3) ∨ (False ∨ p5))) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344105005328336195938974193007 : (p2 → (False ∨ (((p4 ∨ (((p1 ∧ p5) ∧ p3) ∧ ((p2 ∧ p2) → (((p2 ∨ p4) → p4) ∨ p2)))) ∨ ((True → False) → (p3 → p3))) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_652884815119933746351094297799 : ((((p4 ∨ (((p3 ∨ (p5 → (p4 ∨ (((p1 → p2) → False) ∨ (p1 ∧ (p2 ∧ (p4 ∨ True))))))) → (True → p5)) → False)) ∧ (p4 → True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_808907783447519614471685115750 : (((p5 → ((((p1 ∧ p5) → (p1 → (p3 ∧ (p2 ∨ (((p3 ∧ (((False ∨ p1) ∨ False) → (p5 → True))) ∨ p1) ∧ p1))))) → p3) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_756206662965836658211632468535 : (((p1 ∧ (((p4 → (False → ((((True ∨ p1) ∧ p4) ∨ (True → ((True → p5) ∧ p4))) → (p1 → p1)))) → (p2 ∧ p5)) ∨ (p5 ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231740511021456239365515259675 : (((p2 ∧ p5) → p5) → ((p3 ∨ (p5 ∧ (p1 → ((True → p4) ∨ False)))) ∨ ((True ∧ (p3 ∧ (p1 ∨ ((p4 → p3) → (True → p2))))) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1771970364891555020758471846 : ((((p5 ∧ ((True ∧ ((p4 ∧ ((False ∨ p1) ∧ p5)) → (p2 ∨ p2))) → (p2 ∧ p4))) → (p3 ∨ p1)) → p5) ∨ (p5 ∨ (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172283704067918086114119144440 : (((p1 ∨ (((p3 ∧ p1) ∨ p3) ∧ (True ∨ False))) ∨ ((p4 ∨ True) → (True ∧ p2))) ∨ (True ∧ ((p2 → (False ∧ p2)) → ((p2 ∧ False) ∨ True)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57193314381131626402982568942 : ((((p3 ∨ p1) ∨ p3) ∨ ((((p1 ∧ p4) → (p3 ∨ (((True ∧ (p4 ∧ ((p1 → p5) ∧ False))) ∨ (True → True)) → False))) ∨ p3) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349356296260005775493691225266 : (p3 → (p3 → ((p1 ∧ (((False → p3) → False) ∧ (False → ((p1 ∨ p2) ∧ (p5 ∧ p1))))) → ((((p5 ∨ True) ∧ p5) → (False ∧ True)) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261374180479294606758799409762 : ((p5 → p1) → (((((((p2 ∧ True) ∨ p3) ∨ ((((((True → (p5 ∨ True)) ∨ p1) → p5) ∨ p1) ∧ True) ∧ p5)) ∧ p5) ∨ True) ∨ p2) ∨ p4)) := by
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
theorem thm_5_vars_148785119852798280402024458775 : (((False ∧ (p5 ∧ (p1 ∧ (p3 ∨ p3)))) ∨ ((False ∧ p1) ∧ (p5 ∨ (((p3 → p4) ∧ (p1 ∨ p1)) ∨ p5)))) ∨ (p1 ∨ ((p1 → False) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161805744224577884011110573678 : ((p5 ∨ (((p2 → False) ∧ ((p3 ∨ p3) ∧ p5)) ∧ ((p4 → (False ∧ (p5 ∨ p1))) → (p1 ∨ p2)))) → (((p2 ∨ True) → (p5 → False)) → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : (p2 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h4
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h7 := h5 h6
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h15 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h16 : (p2 ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h17 := h2 h16
      -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
      have h18 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h14
      -- We have shown the premise of h17, we can now drive its conclusion.
      let h19 := h17 h18
      -- False on the left can always be used.
      apply False.elim h19
    case inr h20 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h21 : (p2 ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h22 := h2 h21
      -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
      have h23 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h14
      -- We have shown the premise of h22, we can now drive its conclusion.
      let h24 := h22 h23
      -- False on the left can always be used.
      apply False.elim h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248307164373817556750374356155 : ((p2 ∨ p2) ∨ (p1 → (((((p4 → ((p2 ∨ (((True → True) ∧ (p4 ∧ ((True → p2) ∨ p3))) ∨ True)) ∨ p2)) ∧ p5) ∨ True) ∨ p5) ∨ p3))) := by
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
theorem thm_5_vars_230647267481628423550755711432 : (((p3 → False) ∧ p2) → (((p4 ∧ p1) → (p5 → p1)) → ((p2 → False) ∨ (p2 ∨ ((p4 → (((False ∨ False) ∧ p3) → p4)) ∨ (p1 ∨ p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41743219159642984884613073763 : ((((False → (True → (p3 → False))) ∧ ((p4 ∨ ((p4 → p1) ∨ (((p2 ∧ p4) ∨ p2) ∧ (False ∧ (p5 ∨ True))))) ∨ (p2 ∨ True))) ∨ p3) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56193813905178393380297689006 : (((p5 ∧ ((True → p2) → p2)) ∨ ((((((p5 → (p1 ∨ p2)) ∨ p2) ∨ (p4 ∨ (p1 → p5))) → False) → (p5 → (False → p5))) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177851388028227138485745253518 : (((((((p2 ∧ p2) ∨ p3) ∧ ((p3 ∨ True) ∧ True)) ∧ False) ∨ p4) ∨ p2) ∨ (True ∨ (((p4 ∨ True) ∧ ((p1 ∧ p3) → False)) ∨ (p2 ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54958620735798082092829416015 : ((((p2 ∧ (p1 ∨ p4)) ∨ (False → p1)) ∧ ((p3 ∧ ((p2 ∧ ((True ∧ (((p1 ∧ p5) → p1) → (p2 → False))) ∨ p4)) → False)) ∨ True)) ∨ p1) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304017857645833171313133802330 : (p1 ∨ ((False ∧ (((((((p2 ∧ (True ∧ (True → True))) ∧ ((False ∨ (p1 → (False ∨ True))) ∨ True)) ∧ False) → p4) ∧ p2) ∧ p5) → p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



