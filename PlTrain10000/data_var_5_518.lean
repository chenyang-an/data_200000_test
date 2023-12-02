variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_646434512025980410659926515257 : ((((p1 → ((((p3 → (((p4 → p1) → (p3 ∨ p3)) ∨ p3)) → (p1 → (False ∨ True))) ∧ (p3 ∧ (False ∨ (p5 ∨ False)))) ∨ p1)) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342177484427894766770955566045 : (p2 → ((p1 ∨ (((p4 ∧ p5) ∧ ((p1 ∧ p2) ∧ ((p1 ∧ False) → p5))) ∧ (p4 → ((p4 ∨ p1) → False)))) ∨ (((p2 ∧ p4) ∨ p4) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116673051570716476688241550497 : (((p5 → p1) ∧ ((((p5 ∨ (((True ∨ p2) ∧ p2) ∧ (p2 → p5))) ∨ (p5 → p1)) ∨ ((p4 ∨ p1) ∧ p2)) ∨ (True ∧ p1))) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173306171947967844135231411944 : ((p1 → (False ∧ ((p3 → (p1 ∧ ((True → p5) ∨ True))) → ((p3 ∧ p4) ∨ p4)))) ∨ (p5 → (p5 → (((False → p5) ∨ p3) ∨ (p4 ∨ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115135517683720887891317157982 : ((((p1 → p1) ∧ ((((p4 ∨ (p1 → p4)) ∨ False) ∨ p1) ∧ True)) → (p5 → (p5 → ((((p4 ∧ p3) ∨ True) ∧ p1) ∨ True)))) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57875186771068063190413215253 : (((p1 ∨ (p5 ∨ p4)) → ((p4 → p1) ∨ (((p3 ∨ ((False ∨ (p1 ∧ p1)) ∧ True)) ∨ (p4 ∨ ((p4 ∧ False) ∧ p1))) → (p1 ∧ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65393985551637958994958272897 : ((p3 ∨ ((p4 ∨ (p1 ∨ (p1 → (False ∧ p4)))) ∨ ((((p2 ∧ (p5 ∧ (True ∨ (p2 → ((p3 → True) ∧ p3))))) → p2) → False) → p4))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p2 ∧ (p5 ∧ (True ∨ (p2 → ((p3 → True) ∧ p3))))) → p2) := by
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
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h2
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38960286125938356923536004653 : ((((p2 → (p1 → p1)) → ((p1 ∧ ((p2 ∧ (p2 ∨ p2)) ∨ True)) ∧ (p1 ∨ ((p3 ∨ False) ∧ ((True ∨ True) ∨ (p4 ∧ p1)))))) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158057687843217216834807781326 : (((False ∨ ((p1 ∧ p5) ∧ (False ∧ p4))) ∨ ((p1 ∨ (False ∨ ((True ∨ False) → (p2 ∧ p4)))) ∨ p4)) ∨ (((p3 → p3) → (False → p1)) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218287928417954441120318851951 : (((p3 ∨ p3) ∨ (p4 ∨ False)) → ((((p1 ∨ p2) → ((((True → ((p4 → p3) ∧ (False → p5))) → p3) → p2) ∨ (p5 → p3))) ∨ p4) ∨ False)) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h4
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h6
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h7 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h8
        -- One of the premise coincides with the conclusion.
        exact h7
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h10
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h12
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h13 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h14
        -- One of the premise coincides with the conclusion.
        exact h13
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h16
    case inr h17 =>
      -- False on the left can always be used.
      apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_732436364665155452556002498785 : ((((False ∧ p3) ∧ (p4 → ((((False ∨ p4) ∧ (p5 ∨ p5)) → (p3 ∨ ((p2 ∧ p3) ∨ p1))) ∧ (((p2 ∧ p2) ∧ False) ∧ (p5 ∧ True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_724925013765356849986904689732 : ((((p5 ∨ (False → p4)) ∧ (((p3 ∨ False) → ((p4 ∧ (p4 → (((p1 ∨ True) ∨ False) → (p1 → p4)))) → (p2 ∨ p2))) ∨ (p3 ∨ True))) ∨ False) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115707285978149435731831638846 : ((((False ∨ ((p4 ∨ p5) ∨ p3)) ∧ p1) → ((True ∧ ((((p1 ∧ (p2 → p3)) → False) ∧ p2) → (False → p4))) → (p1 → p2))) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260527159014597012869831312260 : ((p3 → p1) → (((p1 ∧ p4) ∨ (((p2 ∧ (((p2 ∨ p4) → p3) ∧ (((p5 → True) → ((p3 ∧ p4) → p3)) → p4))) ∧ p5) ∧ True)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148528606012067578823569441895 : (((((p4 ∧ False) ∨ p1) ∧ ((True → p2) ∧ ((p5 ∨ p5) → p5))) → ((((p2 → False) ∨ p3) ∧ True) ∨ p3)) ∨ ((p2 → p1) ∨ (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51997780352370541909559832562 : (((True ∧ (p4 ∧ ((p1 ∧ (((p5 ∧ p2) ∧ p3) → True)) ∧ ((p5 ∧ p3) ∧ p4)))) ∨ ((p5 ∧ False) ∨ ((p4 ∧ (p4 → p1)) ∨ True))) ∨ p5) := by
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
theorem thm_5_vars_199922314633599067960882953078 : ((((p1 ∧ p1) ∨ (True → p2)) ∨ (p4 → p3)) → ((p2 ∧ False) ∨ (True → ((p5 ∨ True) ∨ ((p1 → (p2 → ((p4 → p4) ∨ p5))) ∨ p4))))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677966826072355786578569315477 : ((((((p5 ∨ p3) ∨ ((((p3 → p2) ∨ p2) → (p1 ∧ ((p4 ∧ p3) ∧ p5))) → p3)) → (True → p5)) ∨ ((p4 ∧ True) ∨ (False → p2))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328090139539544887723343181448 : (True → ((((((p3 ∧ ((((False ∨ True) → p2) → True) ∨ p5)) → (p5 ∨ (p2 ∧ (p1 ∧ p5)))) → False) ∧ p2) ∧ p1) ∨ ((p3 ∧ p4) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219664677612653058772211530674 : ((False → (p2 ∨ (p5 → p5))) → ((p2 → p1) ∨ (True → ((((p4 → ((p2 ∨ (True → p4)) ∨ (False → p5))) → (p2 ∧ p2)) ∨ True) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_626545847470170662378351182525 : ((((p4 → (((p2 ∧ p4) ∧ (p1 ∧ (True ∨ p4))) ∨ (False ∧ (True → ((p5 ∨ ((p5 → (p4 ∧ p1)) ∨ (p2 ∧ p3))) ∨ p5))))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51534397028225958618503043557 : (((True ∧ ((p2 → p2) ∨ ((((p4 ∨ False) ∨ (True ∨ p1)) → p4) ∧ ((p3 ∧ p1) → p3)))) → ((p1 ∧ p3) ∧ ((True → p1) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48055334846366412520312167041 : ((((True → (((p4 ∧ p1) → (p2 ∨ p3)) ∨ True)) ∧ ((((True ∧ (((p2 ∧ p3) ∧ p1) ∧ p4)) ∨ p3) ∧ True) ∧ p4)) → (p2 ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52844268466683130846036351332 : ((((p1 ∧ p2) ∨ (True ∧ (p5 ∨ ((p1 → ((False → p4) ∧ p4)) → p3)))) → (((p3 → (False → p2)) ∧ p4) ∨ (p5 → (True → p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148807534934042596978281166987 : ((((True → (p3 ∨ (False → True))) → True) → ((((p4 ∧ p1) → (False → p3)) → (p2 ∧ True)) → (p1 ∧ p3))) ∨ (True ∨ ((p4 → p3) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135489300154608900945356056540 : ((((p4 → False) ∧ ((p2 ∨ ((p3 ∨ p2) ∧ ((p5 ∨ (p5 ∨ True)) ∨ p1))) ∨ (p2 ∧ p2))) → ((p1 ∨ p4) ∨ p2)) ∨ ((p2 ∧ p5) → p2)) := by
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
theorem thm_5_vars_204580128437928274756632324109 : ((((p4 → p5) ∧ (p4 ∨ p2)) ∨ p2) ∨ (((((p5 → (p4 ∧ p4)) → p4) → (p2 ∨ (p4 ∨ (True ∨ True)))) → p3) ∨ (p1 ∨ (False → True)))) := by
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
theorem thm_5_vars_149691930327098067049401796736 : ((p5 ∧ (((p3 → ((((p1 → True) → (True ∧ p2)) ∨ p4) ∧ p5)) ∨ False) ∨ ((p2 ∨ (False ∨ p4)) ∧ False))) ∨ (True → (True ∨ (False → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319184935677583154564596836551 : (p4 ∨ ((p1 ∨ ((p3 ∨ (((p5 → ((p1 → p5) ∨ p3)) ∨ p3) ∧ ((False ∧ True) ∨ p3))) ∧ p4)) ∨ (True ∨ ((p3 ∨ (False ∧ p2)) → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45866090188441663488081104707 : (((p3 → ((p5 → (((p1 ∧ (p2 ∧ ((((p2 ∧ (p4 → p2)) → p5) → False) ∨ p5))) → p3) ∧ ((p4 ∧ False) ∧ p3))) → p3)) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115655220901385750923460203809 : ((((p4 → (p3 ∧ p1)) ∧ (p4 → p4)) ∨ (((p2 → (p4 → p3)) → (p4 ∨ (True ∧ p3))) ∨ (False → (p5 ∨ (p1 ∨ p1))))) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_623936164721099130916825117028 : ((((p2 ∨ ((False ∨ (p5 ∨ (((((((False ∨ p5) ∨ p5) ∧ (p4 ∧ (p3 ∧ p4))) ∨ p2) → True) → (p3 ∨ p3)) → p4))) ∧ p1)) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_310325775053145834526245006008 : (p2 ∨ ((((p3 ∧ p4) ∨ ((p2 ∨ p1) → (p4 → p4))) → False) → (((p2 → p3) → (p4 ∧ p3)) → (True ∧ ((p3 ∨ True) → (p4 ∨ p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h6 : ((p3 ∧ p4) ∨ ((p2 ∨ p1) → (p4 → p4))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h10 =>
        -- One of the premise coincides with the conclusion.
        exact h8
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h11 := h1 h6
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49214325185433786946458012827 : ((((p5 ∧ p1) ∧ (((((p1 ∨ (p5 → (p2 ∨ p5))) → True) ∨ (p4 → p5)) ∨ (p3 ∧ (False → p2))) → p2)) ∨ (p2 ∨ (p2 → True))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167068887799966365329059264916 : (((((p1 ∨ ((((False → p2) → (True ∧ p5)) ∨ (p2 ∧ p1)) ∧ p4)) ∧ p1) → p5) ∨ p4) → (((p5 → (p5 ∧ p4)) ∨ p1) ∨ (p5 ∨ True))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_882076264328019656364682825395 : (((((((((p3 ∨ False) → ((p3 ∨ p2) ∨ (p4 ∧ p4))) ∧ p3) → (p2 ∨ p4)) ∨ ((p5 ∨ p4) → True)) → (p1 ∧ False)) ∨ (p3 ∧ p2)) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : (((((p3 ∨ False) → ((p3 ∨ p2) ∨ (p4 ∧ p4))) ∧ p3) → (p2 ∨ p4)) ∨ ((p5 ∨ p4) → True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h4
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h3
    -- We need to get the right conjuct of h5 based on <expert-advice>.
    let h6 := h5.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256837035060003970998478894315 : ((p1 ∨ p3) → ((((p5 ∨ (p3 → True)) ∧ (p3 ∨ (p5 → (True ∧ p4)))) ∧ ((p2 ∧ ((p1 → False) ∧ p2)) → p2)) → (p2 ∨ (True ∨ p4)))) := by
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
    cases h6
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_718585532957951230446977267403 : (((((True ∧ p3) ∧ (p4 ∧ True)) ∨ ((False ∧ ((p3 → p3) ∨ p1)) ∨ (p4 → ((True ∧ (p1 ∨ (p1 ∨ p4))) ∨ (p4 → (True ∧ False)))))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233627428054939431229526720662 : ((p2 ∨ (p5 ∧ p2)) → ((((True ∧ (p3 ∨ p5)) → (p3 ∨ False)) ∨ ((False ∨ True) ∨ p3)) ∨ (((True → p3) ∨ ((p1 ∧ p1) → p1)) ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
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
theorem thm_5_vars_38824682579831215031632637921 : ((((True ∨ ((p1 → p2) ∨ p1)) → ((((p4 → (False ∧ (((p2 ∨ p3) → (p2 ∧ p3)) ∨ p4))) → p5) ∧ p2) → (p4 ∨ p5))) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47453460100268368781891156523 : (((p4 ∧ (((((p5 → p4) ∧ (True ∨ (((p2 ∧ p5) ∨ p1) → ((p4 ∨ p3) ∨ p5)))) → False) ∧ p3) ∨ (p2 → p2))) ∨ (p2 ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352049279759816682353071172731 : (p4 → ((False → ((True → ((p2 → p3) ∧ p3)) ∧ True)) → (False ∨ ((p3 ∨ ((p1 ∧ (p1 ∨ p1)) ∨ (((p3 → p5) ∨ p3) ∧ p2))) ∨ p4)))) := by
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
theorem thm_5_vars_324725957925203052532870004768 : (p5 ∨ (((p2 ∨ False) → True) → (True → (((p5 ∧ (p3 ∨ (p4 ∧ True))) ∨ p3) ∨ (((p1 ∨ (p3 ∧ p2)) → (False → True)) ∨ (True ∧ p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44803147685928139351151052304 : (((((p4 ∨ p1) → p4) ∧ (((p4 → (p4 → p3)) ∨ True) → (((((p2 ∧ p5) ∨ p3) ∧ (p5 ∨ (p4 ∨ False))) ∧ p1) ∨ True))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198320773667678692981759088560 : ((p1 ∧ (p3 ∨ ((p1 ∧ p1) ∧ (p2 → p1)))) ∨ (True ∨ ((True → ((True → ((True ∧ p3) ∧ p1)) → (p3 → ((p1 → p4) ∧ True)))) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135492375811206321738674376117 : ((((True ∨ p3) → (((False ∨ ((p2 ∧ p1) → p4)) → p2) ∨ (((p1 ∨ False) → True) → p3))) → ((True ∧ p4) → p3)) ∨ ((p2 ∧ p3) → p3)) := by
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
theorem thm_5_vars_349647785255690187544720502394 : (p4 → (((False ∨ ((p1 ∨ (((p3 → (p3 ∧ p4)) ∨ (p4 ∨ ((p5 ∨ p2) ∨ p5))) → p2)) ∨ (p2 ∨ (p4 ∨ p1)))) ∨ (p2 ∨ p4)) ∧ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208798113121211445494567657548 : ((p2 ∧ (p2 → ((True ∧ False) ∧ p5))) → ((False ∨ (p3 ∨ (((p4 ∨ ((p1 ∧ p3) ∨ (True ∧ (p3 → p1)))) → True) → p3))) → (False ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      let h6 := h1.left
      let h7 := h1.right
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h8 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h9 := h7 h8
      -- We need to get the left conjuct of h9 based on <expert-advice>.
      let h10 := h9.left
      -- We need to get the right conjuct of h10 based on <expert-advice>.
      let h11 := h10.right
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h1.left
      let h14 := h1.right
      -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
      have h15 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h13
      -- We have shown the premise of h14, we can now drive its conclusion.
      let h16 := h14 h15
      -- We need to get the left conjuct of h16 based on <expert-advice>.
      let h17 := h16.left
      -- We need to get the right conjuct of h17 based on <expert-advice>.
      let h18 := h17.right
      -- False on the left can always be used.
      apply False.elim h18
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h19 =>
    -- False on the left can always be used.
    apply False.elim h19
  case inr h20 =>
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h21 =>
      -- Conjunctions on the left can always be decomposed.
      let h22 := h1.left
      let h23 := h1.right
      -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
      have h24 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h22
      -- We have shown the premise of h23, we can now drive its conclusion.
      let h25 := h23 h24
      -- We need to get the left conjuct of h25 based on <expert-advice>.
      let h26 := h25.left
      -- We need to get the right conjuct of h26 based on <expert-advice>.
      let h27 := h26.right
      -- False on the left can always be used.
      apply False.elim h27
    case inr h28 =>
      -- Conjunctions on the left can always be decomposed.
      let h29 := h1.left
      let h30 := h1.right
      -- We want to use the implication h30 based on <expert-advice>. So we show its premise.
      have h31 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h29
      -- We have shown the premise of h30, we can now drive its conclusion.
      let h32 := h30 h31
      -- We need to get the left conjuct of h32 based on <expert-advice>.
      let h33 := h32.left
      -- We need to get the right conjuct of h33 based on <expert-advice>.
      let h34 := h33.right
      -- False on the left can always be used.
      apply False.elim h34



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356867360528405026894933903935 : (p5 → ((p4 ∧ (p2 ∨ (p4 ∧ p5))) ∨ (((p2 ∧ (p4 → ((p3 → (p2 ∨ (p3 ∧ p4))) → p4))) → False) ∨ ((True ∨ (p5 ∧ p1)) ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_82384283373916715067307224543 : ((((p1 ∧ ((p5 → p2) → p4)) ∧ ((p1 ∨ ((p2 ∨ p3) → p4)) → (True → ((p1 ∧ p3) ∧ False)))) ∧ (p1 ∨ ((p3 → False) ∨ p5))) → False) := by
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
  cases h3
  case inl h8 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h9 : (p1 ∨ ((p2 ∨ p3) → p4)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h10 := h5 h9
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h11 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h12 := h10 h11
    -- We need to get the right conjuct of h12 based on <expert-advice>.
    let h13 := h12.right
    -- False on the left can always be used.
    apply False.elim h13
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h16 : (p1 ∨ ((p2 ∨ p3) → p4)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h17 := h5 h16
      -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
      have h18 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h17, we can now drive its conclusion.
      let h19 := h17 h18
      -- We need to get the right conjuct of h19 based on <expert-advice>.
      let h20 := h19.right
      -- False on the left can always be used.
      apply False.elim h20
    case inr h21 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h22 : (p1 ∨ ((p2 ∨ p3) → p4)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h23 := h5 h22
      -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
      have h24 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h23, we can now drive its conclusion.
      let h25 := h23 h24
      -- We need to get the right conjuct of h25 based on <expert-advice>.
      let h26 := h25.right
      -- False on the left can always be used.
      apply False.elim h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191201273714203073257620504016 : ((((p1 → p5) ∨ p3) → (((p4 ∧ p5) ∨ p5) ∧ p2)) ∨ ((p1 → p4) → ((((p4 ∧ p4) → p2) → p2) ∨ ((p5 ∨ p4) → (p1 ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114865220463442777212583910956 : ((((False ∧ (((p2 ∨ (p3 → p4)) → p2) ∧ p5)) ∨ (False → (p5 ∧ p2))) ∨ (p3 ∧ ((False ∨ False) → (False ∨ (True ∨ p3))))) ∨ (p5 ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213911255385950508662884135024 : (((p5 ∨ (p3 ∨ p1)) ∨ p5) ∨ (p4 → ((False ∨ (False ∨ ((((p3 ∧ (p4 → True)) ∧ (p5 ∧ p4)) → True) ∨ (True ∨ p2)))) ∨ (p1 ∨ True)))) := by
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
theorem thm_5_vars_47222637396755950857212964668 : ((((p4 → ((p1 → True) ∧ ((p2 ∨ (p1 ∧ p5)) ∨ p2))) → (p4 ∧ (False ∨ (p3 → (((p4 ∧ p3) ∧ p5) ∨ p5))))) ∨ (p4 ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123414276699154609123818124709 : (((((p3 → p1) → ((((p3 → p3) → p1) ∧ (p5 ∨ p2)) → False)) ∨ ((p4 → p4) → True)) → ((p3 ∨ (p3 ∧ p5)) ∧ p2)) → (p2 ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p3 → p1) → ((((p3 → p3) → p1) ∧ (p5 ∨ p2)) → False)) ∨ ((p4 → p4) → True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65141479930242720168235219773 : ((p2 ∨ (p3 → ((False ∨ (p5 ∨ ((p3 ∧ ((p1 → ((p2 ∨ p3) ∧ p3)) → (False ∧ (p2 → p2)))) ∨ False))) ∨ ((p2 ∨ False) ∨ p3)))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263358585849706208372646802530 : (True ∧ ((p3 ∨ ((p2 ∧ ((p4 ∨ (((False → ((p2 → ((p4 ∧ p1) ∧ p4)) → p2)) ∨ p2) → p1)) ∧ p2)) ∨ True)) ∧ (p4 → (p2 → p2)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199632891694882137314585098614 : (((((p5 → True) ∨ p5) ∨ (p4 → p2)) → p2) → (p2 ∧ ((((p5 ∨ (p5 → (p3 ∨ ((False ∧ True) ∧ p5)))) → p1) → p2) ∨ (True ∧ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p5 → True) ∨ p5) ∨ (p4 → p2)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h5
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : (((p5 → True) ∨ p5) ∨ (p4 → p2)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h6
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204289077446289264149287545856 : ((((p4 ∨ p3) → (p4 ∧ p4)) ∧ p3) ∨ ((p5 ∨ ((p3 ∨ p3) ∨ True)) ∨ (((p4 ∧ p5) → p1) → (p5 → (p3 ∨ (p5 → (p4 ∨ p2))))))) := by
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
theorem thm_5_vars_763881375291767311511300798829 : (((p3 ∧ (p4 ∨ (p1 ∨ (False ∧ (p4 → (False ∨ ((p3 ∨ (p1 ∨ p4)) ∨ ((True ∨ (p1 → (False → p4))) → (False ∧ (False ∧ p3)))))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231749028398428619677444830637 : (((p3 ∧ False) → p2) → ((((False ∨ False) ∨ (False ∧ (p5 ∨ (((p1 ∨ p5) → (p1 ∨ (p4 ∨ p3))) ∨ p2)))) ∨ (False → (p4 ∧ p1))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152065740816783216508384000401 : ((((p1 ∧ p4) ∨ (False → (((p3 ∧ p4) → p4) ∨ p4))) ∨ ((((p2 ∧ p3) ∧ False) ∨ p4) ∨ (True ∨ p1))) → (False ∨ ((p3 ∨ p2) ∨ True))) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Conjunctions on the left can always be decomposed.
        let h12 := h10.left
        let h13 := h10.right
        -- False on the left can always be used.
        apply False.elim h11
      case inr h14 =>
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50404582784669117949479769653 : (((True ∧ ((p2 ∨ ((False ∨ (p1 ∧ False)) ∧ p1)) ∧ ((True ∧ False) → (((p3 ∧ p1) → p3) ∧ p5)))) ∨ (False → ((p1 ∨ p4) ∨ p4))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_629843564370234918999520365966 : ((((((p1 ∨ (p4 ∧ (False ∧ (p1 ∧ (p1 ∧ (p5 → True)))))) ∨ (False ∨ ((True ∧ p2) ∨ (((p3 → p2) ∨ p4) → p1)))) ∨ False) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_169465874772424900778665888793 : (((((p4 ∨ (p3 ∧ p5)) ∨ p4) ∧ (p1 ∨ ((p3 → (True → True)) → p1))) ∨ True) ∧ ((((((p1 → p5) ∧ p4) ∧ p5) → p1) ∨ p1) ∨ True)) := by
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
theorem thm_5_vars_136147051768802672680021018058 : ((((p4 ∧ (False ∨ True)) ∧ ((False → p5) → p3)) → (((True ∧ (p4 → ((True ∨ p1) ∧ p3))) → (p5 ∨ p3)) ∧ p2)) ∨ (True → (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705691507329580706667016697917 : (((((p2 ∨ (p4 → (p4 ∨ p2))) ∧ (p5 ∧ p3)) ∧ (((p1 ∧ ((p2 → p4) ∨ (True → False))) ∨ p5) ∧ ((p5 → p1) ∨ (p2 → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115527716523657522468557395563 : (((True ∧ (p3 → (((p1 → p2) ∨ p5) ∨ p4))) → (((p4 ∨ ((p2 → ((False ∨ (False ∨ p5)) → p5)) ∨ p4)) → p4) → p5)) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57141255620585424108898010766 : ((((p3 → False) ∧ p1) ∨ ((False ∧ p5) ∨ (p4 → (p4 ∧ (((p3 → ((p4 ∧ p5) → (p4 ∧ ((True ∨ p5) ∧ p3)))) ∧ p1) ∨ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_82023740055812031969484492371 : (((((p1 → p4) → p1) ∨ (((p3 → p3) ∧ ((p3 ∨ (True ∨ (p2 → p4))) ∧ True)) ∨ ((p1 ∧ False) ∨ p4))) → ((p5 ∧ p3) ∧ True)) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p1 → p4) → p1) ∨ (((p3 → p3) ∧ ((p3 ∨ (True ∨ (p2 → p4))) ∧ True)) ∨ ((p1 ∧ False) ∨ p4))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59365338347218554356107511781 : (((p5 ∨ p3) ∨ (p3 ∧ (((((p5 ∨ (p2 ∨ (p3 → True))) ∧ p5) ∨ (p3 → ((p4 ∨ ((p4 ∨ True) ∧ p1)) ∨ p3))) → p1) ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261147600772294611093026768642 : ((p4 → p4) → ((((p1 ∨ p3) ∨ (p1 ∧ (((p4 → p1) ∨ p2) ∧ (((p2 ∨ p4) ∨ (p1 ∧ p3)) ∨ p3)))) ∧ False) ∨ ((True ∧ False) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49195606962550333443347360514 : ((((p2 → (p2 → p2)) ∧ (p4 → ((p1 ∧ (p3 ∨ ((p5 ∧ (True → (p5 ∨ p3))) ∧ (p2 ∨ True)))) → p3))) ∨ ((True ∧ p2) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180974383792019367789584048017 : (((p4 → False) ∧ (((True ∨ (p1 ∨ p5)) ∧ False) ∨ ((True → p4) → False))) → (((p4 ∨ True) → ((p5 ∨ p1) ∧ p3)) ∨ ((p4 ∨ p5) → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- False on the left can always be used.
        apply False.elim h6
      case inr h10 =>
        -- False on the left can always be used.
        apply False.elim h6
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h14 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h13
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h15 := h2 h14
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- One of the premise coincides with the conclusion.
      exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165752562784670020028888215396 : (((p3 ∧ (False → (True ∧ False))) ∨ (((True ∨ p1) → p3) → (False ∧ (p4 ∨ (p4 ∧ p2))))) ∨ (False → (p4 → (False → ((p5 ∧ p5) ∧ p2))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h3
  -- False on the left can always be used.
  apply False.elim h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115269868067130087122838086343 : (((p3 ∧ ((p1 ∧ p1) → (p3 → (p1 → (p3 ∧ p2))))) ∨ ((((p2 ∨ (p4 ∧ p3)) ∨ p4) → (p3 ∧ (p2 ∨ False))) ∨ p4)) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302593615266840748179938692975 : (False ∨ (p1 ∨ ((p5 ∨ p4) → ((p3 ∧ (p3 ∨ ((p2 ∧ (p5 ∨ False)) → ((p2 → p5) ∨ (p3 ∨ (p2 → (True ∨ p1))))))) ∨ (False → p2))))) := by
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
theorem thm_5_vars_709363173838740496967757343576 : ((((True ∧ (((p5 → False) ∧ True) → (p5 ∨ p5))) → ((((False ∨ (p4 ∧ (True → ((p5 ∧ p5) ∨ p3)))) ∧ (p1 → p1)) ∧ p4) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40999949829903057043355269707 : ((((p3 → ((p5 ∨ (((p2 → (p3 ∧ p5)) ∨ (p1 ∨ p3)) → p2)) ∨ (((False ∨ (p3 → p2)) ∧ p5) ∧ True))) ∨ (False ∨ p4)) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187120475018017581337575060508 : (((p5 ∧ p2) ∨ (p1 ∨ (((p4 ∨ (p3 → p3)) ∧ p3) ∧ p4))) → (((((False ∧ p3) → p4) → p3) ∨ ((p5 ∨ p4) ∧ False)) ∨ (p4 → p4))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h10.left
      let h13 := h10.right
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h15
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h17
        -- One of the premise coincides with the conclusion.
        exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181697379521561021279915310397 : ((p5 → ((((True → p3) → (p3 ∧ ((p3 ∨ p1) → p4))) ∨ p4) → True)) → (True → (((p4 ∨ ((p1 ∨ p2) ∧ False)) ∨ (True ∨ False)) ∨ False))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52047205942343336482755731076 : (((p1 → (((p2 ∨ (((p2 ∨ (False ∨ p5)) ∧ p1) ∨ p3)) → False) ∧ (p5 ∨ p1))) ∨ (((True ∨ (p4 ∧ p1)) → p2) ∧ (p1 ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707511984403445582510052888649 : (((((p5 ∨ (p5 ∧ True)) ∨ (p1 ∧ (True → p3))) ∨ ((p5 ∧ p4) ∨ (p2 → (True ∨ ((p5 ∧ p3) ∧ ((p5 ∨ p5) ∧ (False ∨ p3))))))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207242602848596782447632933285 : ((((False ∧ (True ∨ p2)) ∨ True) ∨ p3) → ((p2 ∨ (False ∨ (((False ∨ p3) → p1) ∧ p2))) ∨ (p1 → (((p3 ∧ p4) ∧ p5) → (p2 ∨ p3))))) := by
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
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h9.left
      let h12 := h9.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h11
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h14
    -- Implications on the right can always be decomposed.
    intro h15
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- Conjunctions on the left can always be decomposed.
    let h18 := h16.left
    let h19 := h16.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_706488632577469043820372183483 : ((((p4 ∨ ((True ∧ p4) → ((p3 → p3) → False))) ∧ ((((((((p2 ∧ p1) → p2) ∨ (True ∧ p2)) ∧ p3) ∧ False) ∧ p4) → False) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148799215168098162221961660288 : ((((p1 ∨ (p4 → (p2 → False))) ∧ p2) → ((p4 ∧ ((p1 ∧ p2) ∧ (True ∧ p4))) ∨ (False → (p4 → True)))) ∨ (True ∧ (p4 → (True → True)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53871671471169000906857714111 : ((((p4 → p3) ∧ (p4 → (True → ((p4 → p5) ∨ p1)))) ∨ (p2 → (p1 ∨ (((False → ((p1 ∧ p2) ∨ p2)) → (False ∧ p4)) ∨ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55693779843681833854656273947 : (((((False → False) → p2) ∨ p4) ∧ (((((p3 ∨ True) ∧ (False ∨ p1)) → (p1 ∧ (p2 ∨ True))) → ((p2 ∨ p4) ∨ (p1 → p5))) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148806303695398651629791371034 : (((((p4 ∨ False) → (p3 ∧ False)) → p4) → (((p3 → (((False ∧ True) → p3) ∧ True)) ∧ (p1 ∨ p5)) ∨ p1)) ∨ (True ∨ ((p3 ∧ p4) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304029533328040501913810580415 : (p1 ∨ ((p2 ∧ ((True ∨ ((p2 ∨ (p3 ∧ True)) → ((p5 ∧ (p3 → p1)) → ((p4 ∧ p3) → (p2 ∨ (p4 → (p3 → False))))))) → p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191841890468923417970412273485 : ((p3 ∨ ((p4 ∨ p3) ∧ (p5 ∧ (p4 → (False ∧ False))))) ∨ (((((True ∧ (p3 → (p2 → p2))) ∧ p5) ∧ p3) ∧ ((p3 → False) ∨ p5)) → p5)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h10 =>
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h11 =>
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37455243023109744466903163216 : ((((((p2 ∧ False) → (p4 ∨ ((p1 ∨ (False → p3)) ∨ (True ∧ True)))) → (p4 ∧ (((True ∨ (False → p1)) ∧ False) → False))) ∨ p4) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198260270460426746197006973099 : ((False ∧ ((p4 ∨ ((p2 ∧ True) ∨ p1)) ∨ p5)) ∨ ((p1 → (((False ∧ p5) ∧ p4) → ((False → p3) → ((p2 ∧ p5) ∧ (p5 ∨ p1))))) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the left can always be decomposed.
  let h8 := h2.left
  let h9 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- False on the left can always be used.
  apply False.elim h10
  -- Conjunctions on the left can always be decomposed.
  let h12 := h2.left
  let h13 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h12.left
  let h15 := h12.right
  -- False on the left can always be used.
  apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_735709357258861201221017780404 : ((((p5 ∨ p3) ∧ (((((False → False) ∨ ((p2 → p3) ∧ (True ∨ (p2 → False)))) ∨ ((p4 ∨ p3) ∧ p1)) → (p4 → (p5 → False))) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116108687784346073861345446676 : ((((False ∨ False) → p4) ∧ ((p3 → ((((p4 ∨ p3) → ((False ∨ (True → (p3 ∨ p4))) → False)) → p4) → (p2 → False))) ∨ False)) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174217634452589812316158446174 : (((((((p4 → p4) → True) → False) ∧ p1) ∨ ((False → False) ∧ p2)) → (p2 ∨ p5)) → (((p1 → p2) ∨ True) ∨ (((p3 ∨ True) → p4) ∧ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157198575684428848072281618789 : (((((True → ((True ∨ (True ∨ (True ∧ p4))) ∧ (p4 ∧ (True → p3)))) ∧ p1) ∨ (True → p1)) → False) ∨ (p3 → ((True → p3) ∨ (True ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_706273853038806907809365595282 : ((((p3 ∧ ((True ∨ (p3 → (p2 ∧ p2))) ∧ p4)) ∧ (False ∧ ((p1 ∨ (p2 ∧ ((p3 ∨ True) ∨ p5))) ∧ (p1 ∨ (p2 → (True → p5)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358096468468127836177555143943 : (p5 → (p2 ∨ ((((p5 → (True ∨ p4)) → p2) ∨ (p3 → ((p5 ∧ p3) ∧ ((False ∨ (True → p2)) → ((p2 ∨ False) ∧ (True → p2)))))) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h7 := h5 h6
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h11 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h12 := h10 h11
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_634357740709011067359276727747 : (((((((((((((p1 → p4) ∧ (p1 ∨ p3)) ∨ p2) ∨ (p2 ∧ p5)) → True) ∨ False) ∨ True) → p1) ∧ p1) ∧ ((p2 → True) → True)) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



