variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54469277377049989455192400699 : ((((((p1 ∨ p5) ∧ p4) → True) ∧ (p5 ∨ p1)) ∨ (((p5 ∧ p3) ∧ (((p2 → (False → p5)) → (True → False)) ∨ p2)) ∧ (p3 ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148708246231959598364213965867 : ((((p5 ∨ ((p4 ∧ p2) ∨ (True ∧ p3))) → p3) → (p3 ∧ (False → ((((p2 → False) → p5) ∧ p4) → p2)))) ∨ (p4 → (p5 ∨ (p4 → p4)))) := by
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
theorem thm_5_vars_137536796756943777054573684665 : ((p5 ∧ (p5 ∨ ((p3 ∧ (p1 ∨ ((True ∨ p1) ∨ ((((p2 → (False ∨ (p5 ∨ True))) → True) ∨ p3) ∨ p3)))) ∨ p5))) ∨ ((p3 ∧ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65782724643926381567709283862 : ((p4 ∨ ((((p3 ∨ (p3 ∧ (p2 → ((p2 ∨ p1) ∨ p4)))) ∨ False) ∨ (p4 ∧ p2)) → ((True ∨ p3) ∧ ((p2 → (True → p2)) → p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41982121129105938835130234052 : ((((p3 ∨ p3) ∧ ((False ∧ (((p1 ∧ ((p3 ∨ p2) ∨ p4)) ∧ False) ∧ (p5 ∧ (False ∧ p1)))) ∨ (((True ∧ p1) ∧ True) ∨ True))) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179335400995512478418445758939 : ((p1 ∨ (((p3 ∨ p3) → (False ∧ False)) ∧ (((p5 → p2) ∧ p1) → False))) ∨ ((p1 ∨ ((((p2 ∧ p3) ∧ True) ∨ True) ∧ True)) ∨ (p3 → False))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217490330422053583429455793467 : ((((p5 ∧ p4) ∧ p5) → p5) → (True ∧ (True ∧ ((p1 → p2) ∨ ((True → (p3 ∨ ((p2 ∨ ((p5 ∧ False) → p2)) ∧ p3))) ∨ (p2 → True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57909195141026894760315104241 : (((p4 ∨ (False → p3)) → (((True → ((p2 ∧ ((p5 ∧ p4) ∧ (True ∧ ((p2 ∧ p1) ∨ p4)))) → (p2 ∧ True))) ∧ True) ∧ (p5 ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695251679193780193747977365147 : ((((((p5 ∨ ((((True ∧ True) ∨ (False ∧ False)) ∧ p2) → p5)) ∨ p4) → p1) → ((((p1 ∧ p1) ∨ (False ∨ p3)) → p2) ∨ (p3 → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251549568480189180074845416378 : ((p3 → False) ∨ ((p2 ∨ (((p1 ∧ (p5 ∧ p5)) ∧ p1) ∨ (((p2 ∧ False) ∧ (p5 → (p4 → ((p1 ∨ p4) ∨ True)))) → p4))) ∨ (True → p2))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699569801244448964154640889693 : (((((((p2 ∨ True) ∨ (p2 ∨ ((p5 ∧ p2) → p5))) ∧ p3) → False) → ((((True ∨ ((p2 → (False ∨ p5)) ∧ p2)) → p5) ∧ p2) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46446134823863123946192426894 : ((((p4 ∨ (p3 → (False → p2))) ∧ ((p3 ∨ p3) ∧ (((True → True) → (((p5 ∧ p1) ∧ False) ∧ False)) ∨ (True ∧ True)))) ∧ (p3 ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56354575187620046176577538227 : ((((p3 ∧ (p3 ∨ True)) ∨ p5) → (p1 ∨ ((((p3 → p1) → False) ∧ (True ∧ False)) ∨ ((((p1 → p5) → (p2 ∧ p2)) → p5) → p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118883476887807143359401998572 : ((True → (False ∧ (((((p2 ∨ p5) ∨ (p3 ∨ (p5 ∨ True))) → False) ∧ ((p3 → (p3 → (False → (p4 ∧ p1)))) ∨ p2)) → p5))) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_766900818561863735334352300890 : (((p4 ∧ (p5 ∨ (p2 → (p5 → ((((p2 → p5) ∧ (True ∧ p4)) → (True → ((p5 → p4) → (p2 ∧ ((p5 ∨ True) → False))))) ∨ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49040755614726647435986801926 : ((((p2 ∨ (p5 → (((((p2 ∨ (True → p3)) → ((p5 ∧ p1) ∧ p3)) → p5) ∧ p2) ∧ (False ∧ p5)))) → False) ∨ ((False → p1) ∨ p5)) ∨ p5) := by
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
theorem thm_5_vars_50139899661239707731745541782 : (((True → (((((p1 → p4) ∨ p4) ∧ False) ∨ p1) → ((p5 ∨ (((p2 ∨ p5) ∨ p2) → False)) ∧ True))) ∧ ((p5 ∧ p2) ∨ (True ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313968225116780720627690645099 : (p3 ∨ ((((p2 ∨ ((p3 ∧ p2) ∧ (p5 ∨ p5))) ∧ (p1 → ((False ∧ p3) → (p2 → p5)))) ∨ ((True ∧ False) → (p3 → True))) ∨ (p1 → p2))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148330203796291378091941863730 : (((((p4 → (p5 → (((p1 ∨ p2) ∧ True) → p1))) → (p5 ∧ p1)) ∨ p5) ∧ (((True ∨ p3) ∨ p3) ∨ p2)) ∨ ((True ∨ p5) ∨ (p2 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150193291410941855527126024195 : ((p2 → (((p4 → False) → ((p1 → p4) → ((False → p1) → (p1 ∧ (((p1 ∨ p4) → p2) ∧ p1))))) ∨ False)) ∨ ((False ∧ p3) → (p5 ∧ True))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38913376989859186071626216393 : ((((True → (p4 ∨ p2)) ∨ (p2 ∨ ((p5 ∨ ((p5 ∧ ((p3 → ((False ∨ p2) ∧ (p2 ∨ p4))) ∧ False)) → (p2 ∧ p4))) → p2))) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38344039890858095329900364379 : (((((p5 ∧ False) ∧ ((p5 ∧ ((p3 ∧ (p1 ∧ False)) ∧ True)) ∨ (p5 → (p4 ∧ False)))) ∧ (False → (True ∧ (True ∨ (False ∨ False))))) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1797078776920295924492763835 : (((p4 ∨ (True ∨ p2)) ∧ (p5 ∧ (((p1 → False) → (((p4 ∨ p2) ∧ True) → False)) ∧ ((False ∨ p5) ∨ False)))) ∨ (p1 → (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355873790049065717200412107295 : (p5 → (((p4 → False) ∨ (((p5 → (p3 ∧ p2)) ∧ p1) ∧ ((p2 ∨ p3) → ((p2 ∧ True) ∨ (False ∧ (True ∨ p2)))))) ∨ (True → (p5 ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51156330777523115784701305174 : ((((p2 ∨ (((((False ∨ (p2 → p4)) ∨ p3) ∧ ((False ∧ True) ∨ p4)) → True) ∨ True)) → p3) ∨ ((p3 ∧ (p5 → (True ∨ p5))) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179698759288798908732517577015 : (((((((p5 → (p5 ∨ p2)) → p1) → (p2 → False)) → p1) ∨ p4) ∧ True) → (((p1 ∧ (p1 ∨ p1)) → (p2 ∧ True)) ∨ (p1 → (p3 → p3)))) := by
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
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_700586854082072731186781138169 : ((((False → ((False ∨ p1) ∨ ((p2 → (True ∨ p1)) → (True → p4)))) → ((((p3 ∨ (p5 ∨ (True → p3))) ∨ (False → p1)) ∧ p5) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244251430472771443648301970070 : ((False ∧ True) ∨ (((p3 → (p3 ∧ p5)) → (((False ∨ (p5 → True)) ∧ p4) → ((p2 → ((p1 ∨ (p3 → (p1 ∨ True))) ∨ p4)) ∧ False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339663562590256905888931294118 : (p1 → (p3 ∨ (((((p4 → (True ∨ p1)) → p3) ∧ (p2 ∧ (True ∧ ((p5 ∧ (p3 ∧ ((p4 → p2) ∨ p5))) ∧ True)))) ∨ (p5 → p4)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_398493940806631456365793632859 : ((((True → ((((p5 ∨ p5) ∨ (((p2 ∨ p5) → False) ∧ ((((p4 ∧ p1) → p3) → (p2 → (p3 ∨ p5))) ∧ p1))) → False) ∧ p3)) ∨ True) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200909146510307210394674159526 : ((p1 ∨ ((True ∨ ((p1 → False) ∨ p5)) ∧ p4)) → (((((True → p5) ∧ True) ∨ (((p4 → True) → p2) ∧ p5)) ∧ p3) → ((p2 ∨ False) ∨ p5))) := by
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
    cases h1
    case inl h8 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h9 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h10 := h6 h9
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h14 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h15 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h16 := h6 h15
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h16
      case inr h17 =>
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h18 =>
          -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
          have h19 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h6, we can now drive its conclusion.
          let h20 := h6 h19
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h20
        case inr h21 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h21
  case inr h22 =>
    -- Conjunctions on the left can always be decomposed.
    let h23 := h22.left
    let h24 := h22.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h25 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h24
    case inr h26 =>
      -- Conjunctions on the left can always be decomposed.
      let h27 := h26.left
      let h28 := h26.right
      -- Disjunctions on the left can always be decomposed.
      cases h27
      case inl h29 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h24
      case inr h30 =>
        -- Disjunctions on the left can always be decomposed.
        cases h30
        case inl h31 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h24
        case inr h32 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h32



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_804405762573250451277402260718 : (((p3 → (((p5 ∨ (p3 ∧ (False ∨ False))) ∨ ((True ∨ p2) ∧ p2)) ∨ (((True ∨ p2) → p3) ∧ (True ∧ ((p1 ∨ (p1 ∨ True)) ∨ False))))) ∨ p3) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_257633810628979969096858208459 : ((p3 ∨ p2) → (((True ∧ p1) → ((True → ((p2 ∨ p2) ∧ False)) ∧ p1)) ∨ (p5 → ((p4 → ((p1 ∧ p1) ∨ False)) ∨ ((p3 ∨ p1) → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133107443836275860521042208702 : ((True → (True → ((p4 ∨ (p4 ∨ ((True ∧ p4) ∧ p1))) ∨ ((((p3 ∧ (p5 ∧ False)) ∨ p4) ∨ True) ∧ (True ∨ True))))) ∧ ((p3 → True) ∨ False)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135301945174360577946593028573 : (((((p3 ∧ (((p4 ∧ True) ∨ p5) ∨ p1)) ∨ (((p3 ∨ (True ∧ p5)) → False) ∧ p2)) ∨ p1) ∧ (p4 ∧ (p4 → p2))) ∨ ((False ∨ p2) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624404338263117188594434590421 : ((((p3 ∨ (p3 ∧ ((((((True → p1) ∧ p3) ∧ True) ∧ p5) ∨ ((p1 ∨ (False → p4)) → ((p4 → p2) ∧ False))) ∧ (p2 → p5)))) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57440754104639625451693051440 : (((p4 ∨ (p4 ∧ True)) ∨ ((((((p3 ∧ True) → ((True ∧ True) → p5)) ∨ (p4 ∧ ((p3 ∨ p4) → p1))) ∨ False) → False) ∨ (p2 → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191642681059121271690925748931 : ((p4 ∧ (((p2 ∧ True) → (p2 ∧ p2)) → (p3 → p2))) ∨ (p4 → ((((p4 → (p2 ∧ (p2 ∧ False))) ∨ (p5 ∧ p4)) ∨ p2) → (p1 ∨ p4)))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343818868566799337872062359950 : (p2 → (p2 ∧ ((p4 → (p3 ∨ ((((False ∧ ((p3 → p2) ∨ (True ∧ (False → True)))) ∧ p3) → p4) → False))) ∨ (p3 ∨ ((p2 ∨ p4) ∧ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113582296677403738776652283306 : (((p1 ∧ (p1 → (p2 ∨ (((True ∧ ((p3 ∨ p5) ∧ (p4 ∨ p1))) ∧ (p1 ∧ p5)) ∨ ((True → p5) ∧ p1))))) ∨ (p2 ∨ p1)) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117229902867262184883576055921 : ((True ∧ (True ∧ (p5 → (((True → p2) ∨ p2) → (p3 ∨ (p1 ∧ (((True ∨ (p5 → p2)) ∧ False) ∨ ((False ∨ p4) → p4)))))))) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350123381419139049566845494623 : (p4 → (((((p5 ∨ p2) ∨ (p1 ∧ p4)) ∨ (p2 ∧ (p3 → (p5 → (p1 ∨ (False ∨ p1)))))) ∨ (p4 ∨ (p4 → ((p4 ∨ p4) → p1)))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115842929499757621549599645882 : (((p4 ∧ (p5 → (p2 → p1))) ∧ (((True → ((True ∨ p3) → p5)) ∧ p5) ∧ (((p3 ∨ p3) → ((True ∧ p5) ∨ p3)) ∨ True))) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48546126498101667503032910729 : ((((((((True ∨ (p1 ∨ ((p4 ∨ True) → p1))) ∨ True) → False) ∧ ((p1 → (False ∧ p2)) ∧ p2)) ∨ True) → p5) ∧ (p4 ∨ (p4 ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_91172891724138341397132607073 : (((p5 → p3) ∧ (((((p1 ∨ (p4 → p1)) ∧ (((p4 → p1) ∨ False) → p4)) → p1) ∨ ((True ∧ (p5 ∨ p4)) ∧ True)) ∧ (p5 ∧ True))) → p3) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h9 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h10 := h2 h9
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h12.left
    let h15 := h12.right
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h5.left
      let h18 := h5.right
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h19 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h17
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h20 := h2 h19
      -- One of the premise coincides with the conclusion.
      exact h20
    case inr h21 =>
      -- Conjunctions on the left can always be decomposed.
      let h22 := h5.left
      let h23 := h5.right
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h24 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h22
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h25 := h2 h24
      -- One of the premise coincides with the conclusion.
      exact h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323895711297448616290489175777 : (p5 ∨ ((((((((True ∧ p3) → p4) ∨ p2) → True) ∨ False) ∧ (p2 ∨ p1)) → (p1 ∧ p3)) ∨ (((p4 ∧ False) ∧ ((False ∧ p4) → False)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_586538767584333586261734955726 : ((((((True ∨ p1) ∧ ((p5 → ((p4 ∧ p2) ∧ (((p5 → (p3 ∧ ((p4 ∧ p5) → p1))) ∨ False) ∧ p4))) ∨ (True ∧ p3))) ∧ p1) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55399541560039262912299805403 : ((((p5 → ((p3 ∨ p3) → p2)) ∧ p5) → (p2 → ((((p2 ∧ ((p1 ∨ (True ∧ p1)) → (True ∧ p4))) → p2) → p2) ∨ (p3 → p5)))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_836747373932952849521528533068 : (((((((p5 → ((p1 → ((p4 → (p1 ∧ True)) → (p3 → (p5 → (p2 → p5))))) → (p2 ∧ p5))) → (p4 → p3)) ∨ True) → False) ∨ False) → False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : (((p5 → ((p1 → ((p4 → (p1 ∧ True)) → (p3 → (p5 → (p2 → p5))))) → (p2 ∧ p5))) → (p4 → p3)) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h4 := h2 h3
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179917964987978239182279564417 : ((((p2 → ((((p5 → False) ∧ p4) → p3) ∧ (p4 ∨ p1))) ∨ False) ∨ p5) → (((p2 → (p2 → (p5 → p1))) ∧ p4) ∨ ((False → p1) → True))) := by
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
      -- Implications on the right can always be decomposed.
      intro h4
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- False on the left can always be used.
      apply False.elim h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165322692315986957959487276587 : (((((((p1 → (p2 → False)) ∧ (p3 ∧ p1)) ∧ p5) ∧ p1) ∧ p2) ∧ ((p3 → True) ∨ p5)) ∨ (((p5 ∧ p1) → (True ∨ p1)) ∨ (True ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153249470914759032721623590600 : ((False ∨ ((False ∨ ((((p2 → (True → (p4 ∨ False))) ∧ ((p4 ∨ p4) ∨ p1)) ∨ (p1 ∧ p5)) ∧ False)) → p4)) → (((True ∨ p1) → p4) → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : (True ∨ p1) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316511038081515077606473939448 : (p3 ∨ (p2 ∨ ((((p3 → p3) → (p1 → ((p5 ∨ p5) → p3))) ∨ p5) ∨ (((False → (p4 ∧ True)) ∧ False) → (p2 ∧ (p1 ∨ (p1 ∧ p1))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  apply False.elim h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_585956646650411387316171293199 : ((((((((p4 → False) ∨ p5) ∧ (((True ∧ p5) ∨ p5) ∨ ((p3 ∧ (p5 ∧ ((p3 ∨ p4) → p1))) ∨ True))) → (p3 ∧ p1)) ∧ p3) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326310523035365128638818659520 : (p5 ∨ (p4 → (((p4 ∧ p2) → p1) ∨ (((((((p5 ∨ p3) ∨ p5) ∨ p3) ∧ ((p1 ∨ p2) ∨ (p3 → (True → True)))) → p1) → p2) ∨ True)))) := by
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
theorem thm_5_vars_66609733924672612507543885409 : ((True → ((p4 ∨ (p1 ∨ ((((p4 → ((False ∧ p3) → p3)) → (False ∧ (p5 ∧ p1))) ∨ True) ∨ p2))) ∨ ((True ∨ False) ∨ (p4 ∧ p4)))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_161940953332245863461392891625 : ((p2 → (((p4 ∨ (p1 ∨ ((((False → p3) → (p3 ∧ p2)) → (p3 ∨ p4)) ∧ p2))) → p4) ∨ p2)) → ((p2 ∨ (p3 ∨ (p4 ∨ p2))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1812684117863089150303551112 : ((False ∨ (p4 → ((p4 → p5) ∧ (p4 ∧ (((True ∧ (p1 ∨ False)) → p5) → ((p5 → (p3 ∧ p3)) → p3)))))) ∨ (False → (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146958920689624999906943501685 : ((((p3 ∨ (((((((p3 ∧ False) ∧ p5) → True) → p5) ∧ p2) ∨ ((p3 ∧ p4) ∧ p2)) ∨ p3)) ∨ p2) ∧ p5) ∨ (True ∨ (False ∨ (p3 ∧ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149112956246438869860497411918 : (((True ∧ p1) ∧ (p5 ∨ (p2 ∧ ((p2 ∨ (((p3 ∨ (p2 → ((p5 ∨ p4) ∧ p2))) ∧ p4) ∨ p4)) ∨ p3)))) ∨ (((p4 → p4) → False) → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p4 → p4) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_951045089173381879797214681909 : ((((False ∨ (p1 ∨ p1)) ∧ ((False ∨ ((False ∨ False) ∨ p5)) ∧ (((p1 ∧ (False ∧ p4)) ∨ (((p2 → p3) → (p3 ∨ True)) → p5)) → p4))) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h3.left
      let h8 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- False on the left can always be used.
        apply False.elim h9
      case inr h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Disjunctions on the left can always be decomposed.
          cases h11
          case inl h12 =>
            -- False on the left can always be used.
            apply False.elim h12
          case inr h13 =>
            -- False on the left can always be used.
            apply False.elim h13
        case inr h14 =>
          -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
          have h15 : ((p1 ∧ (False ∧ p4)) ∨ (((p2 → p3) → (p3 ∨ True)) → p5)) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h16
            -- One of the premise coincides with the conclusion.
            exact h14
          -- We have shown the premise of h8, we can now drive its conclusion.
          let h17 := h8 h15
          -- One of the premise coincides with the conclusion.
          exact h17
    case inr h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h3.left
      let h20 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h21 =>
        -- False on the left can always be used.
        apply False.elim h21
      case inr h22 =>
        -- Disjunctions on the left can always be decomposed.
        cases h22
        case inl h23 =>
          -- Disjunctions on the left can always be decomposed.
          cases h23
          case inl h24 =>
            -- False on the left can always be used.
            apply False.elim h24
          case inr h25 =>
            -- False on the left can always be used.
            apply False.elim h25
        case inr h26 =>
          -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
          have h27 : ((p1 ∧ (False ∧ p4)) ∨ (((p2 → p3) → (p3 ∨ True)) → p5)) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h28
            -- One of the premise coincides with the conclusion.
            exact h26
          -- We have shown the premise of h20, we can now drive its conclusion.
          let h29 := h20 h27
          -- One of the premise coincides with the conclusion.
          exact h29
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116877440719552799605253967557 : (((p2 → p5) ∨ (((True → (p4 ∧ ((False ∨ (p3 ∧ (p3 ∨ p4))) → (False ∨ p2)))) ∧ (((p2 → p4) → p5) ∨ p2)) ∨ False)) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_203677313522420489263858986654 : ((p3 ∨ (p1 → (p3 ∨ (p4 ∨ True)))) ∧ (((p3 → ((p2 → (True ∨ False)) ∨ p3)) → (p5 ∧ ((p3 ∨ (p2 ∧ p1)) ∨ (p5 ∨ False)))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43353054338939784470296732201 : (((((((((p5 ∧ False) ∨ (False ∨ ((False → True) ∨ p5))) → (p3 ∨ p4)) → p2) → (p3 ∨ (p4 → p3))) ∧ (p3 ∨ p5)) ∨ p4) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49036292061084798438928195321 : ((((p2 ∧ (((((False → p2) ∧ True) ∧ (p5 → p3)) ∨ p2) ∧ ((p5 ∨ p2) → (p3 ∨ (p2 ∨ p4))))) → False) ∨ (True ∨ (True → True))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173130072156363035702211305062 : ((p2 ∨ (p2 ∨ ((p3 → True) ∧ (((p4 ∨ (False ∨ (p5 → p2))) → p5) → False)))) ∨ ((p4 ∧ (False ∧ p2)) → ((p5 ∨ (True ∧ p4)) → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h1.left
    let h12 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136835544720452153325336913791 : (((p1 ∧ p3) ∨ (((True → (p1 ∨ (p3 ∨ p5))) ∨ ((True ∧ (p1 ∧ (p5 → (p1 ∧ p2)))) ∧ p5)) ∨ (False → p1))) ∨ ((p2 → True) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310851830875691708920567478281 : (p2 ∨ (((True ∧ p3) → p3) → ((((False ∨ p3) ∨ p5) ∧ (p1 ∧ (False → ((p5 ∨ p2) → p3)))) ∨ (((p3 → True) ∨ False) ∨ (p3 ∨ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116216131336912075924043185275 : ((((p5 ∧ p4) ∨ False) ∨ ((((p1 ∧ (p2 ∨ p5)) ∧ ((True ∨ ((p1 ∧ True) ∨ ((p1 ∨ False) → p2))) ∧ p3)) ∨ p3) ∧ p3)) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119336187159954446103422758996 : ((p3 → ((p2 ∧ (False ∧ (p1 ∨ p5))) ∧ ((((((p1 → p5) → ((p5 ∧ (p5 → p1)) ∨ p2)) ∧ p4) → p2) → p5) ∧ p5))) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2435467031423441534431855453 : (((p2 ∧ p3) ∨ (((p2 → p5) ∧ p4) ∨ (p5 → True))) ∧ ((True ∧ ((p4 → False) ∧ ((False ∧ ((False ∧ True) ∨ p1)) ∧ p2))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610382883244887992885384739819 : (((((((p2 → (p4 → ((p3 ∧ (False ∨ (p1 → p3))) ∧ (((((True → False) ∧ p5) ∧ True) ∨ True) → p2)))) → False) → p4) → p5) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336196893405608137988772538896 : (p1 → ((((((((((p5 → (p1 ∨ ((True → p2) ∧ (p3 ∨ p3)))) ∧ p2) → p1) ∧ True) ∨ p4) → p1) → p1) → p3) ∨ (p5 ∧ True)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214540588286496163503458946926 : (((True ∨ p3) ∧ (p2 ∨ p5)) ∨ (((((((True ∨ False) → True) → p2) ∨ p2) ∨ (p3 → (p5 → (p2 → p3)))) ∧ True) ∧ (False → (p4 ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151978570319527984651364189276 : (((p4 ∨ (p5 → (p1 ∨ ((((p4 → p4) ∨ p5) ∨ p1) → True)))) ∨ (p3 → (p4 → ((p5 ∧ p4) ∨ p3)))) → ((False ∧ (False ∨ p1)) ∨ True)) := by
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
theorem thm_5_vars_209134847564642877189813125233 : ((p3 ∨ ((p5 → (True ∨ True)) ∧ p3)) → (((p3 ∧ ((p5 ∨ p4) ∨ p2)) → ((p3 ∨ p1) → p5)) → (p3 ∧ (((p3 ∧ p5) → p4) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h6
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351484510222097906303876477911 : (p4 → (((p5 ∨ (p4 → ((((p2 ∨ p1) ∨ p3) → (p3 → (False ∨ (p1 ∨ p3)))) ∨ False))) ∨ True) ∧ (p4 ∨ (((p2 ∨ p4) ∨ False) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690563271169887570535731244895 : (((((((p5 → (p3 → True)) ∨ ((p2 ∨ ((p2 ∨ True) ∧ p4)) ∧ True)) ∧ p1) ∨ True) → ((p5 → p4) → ((p5 ∨ p2) ∨ (p2 ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38465974557437253390942018935 : ((((p4 ∧ (p3 ∨ (p3 ∧ (((p1 ∧ ((p1 → False) ∨ p3)) ∧ p5) ∧ p2)))) → (((p5 ∧ ((p1 ∧ True) ∨ p1)) ∧ p5) ∨ p3)) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42167032683661804815035896099 : ((((p4 → p5) → (p2 ∧ ((p1 ∨ ((((p4 → p2) ∧ (((p1 → (True ∨ True)) ∧ (p4 → False)) ∧ True)) → p5) ∨ p2)) ∨ True))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59188778578720500271699925493 : (((p1 ∨ False) ∨ (((((p2 ∨ (((p3 → (False ∧ False)) ∨ p1) → p5)) ∧ (p4 → p1)) → (p1 ∨ p2)) ∧ p1) ∨ (p2 → (p5 → p5)))) ∨ p5) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166466518940489932496311849158 : ((p2 ∨ (p3 ∨ (p5 ∧ (p1 ∨ ((p1 ∨ ((p1 ∨ (p3 → p2)) → p5)) ∧ (False ∨ p5)))))) ∨ ((((p4 ∨ p1) ∧ p2) ∨ (p1 → p1)) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47867266124032702366342878744 : ((((((p3 ∨ ((((True ∨ (True ∧ True)) → p5) → p3) → p4)) → p2) ∨ ((False ∧ p5) ∨ (p3 ∨ p4))) ∧ (p5 → p4)) → (True → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330527864752175195620697679421 : (True → (p4 ∨ (p1 → (((((p1 ∧ (p3 → (p4 ∧ False))) ∧ p3) ∧ p5) ∨ (p1 ∨ p1)) ∨ ((True → p1) ∨ (True ∧ ((True → True) ∧ False))))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60419155771385416606594704886 : (((p4 → p2) → ((p1 → (p4 → (p4 → (((True ∧ ((((((False → p1) → p1) ∧ p4) ∨ p2) → True) ∨ p1)) ∨ p1) ∧ p5)))) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698026699223710545724730268805 : (((((((((p2 → True) ∨ p1) ∧ p3) ∧ p4) ∧ (p3 → p4)) ∨ p5) ∨ ((p2 ∨ ((p2 → p5) → (True → (False ∧ False)))) ∨ (p1 ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56753486048215008633948898314 : ((((p2 → p3) ∨ p2) ∧ ((p1 ∨ p1) ∨ ((True ∨ p4) → (p3 ∨ (((p5 ∧ p1) ∨ ((((False → p5) ∧ True) → p4) ∧ True)) → p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200377311223979951187736904749 : (((p4 → p4) ∧ (p4 ∧ ((p4 ∧ p4) → False))) → (p3 → (False ∨ (p3 ∧ (((p4 → ((((p3 → True) ∧ p3) → p3) ∨ p5)) → False) ∧ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : (p4 ∧ p4) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h5
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h8 := h6 h7
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_805812591212036385852470929669 : (((p3 → (p4 → (True ∧ (((((p4 ∨ p2) ∨ ((True ∧ (p1 ∨ False)) → False)) → False) ∧ p3) ∧ (False ∧ (False → ((p4 ∧ p5) → p3))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610852490856357094219067351508 : (((((((((p3 ∨ (p3 ∧ (p3 ∧ p3))) ∨ ((p1 ∨ False) ∧ p5)) → p1) ∨ False) → (((p1 ∧ p3) ∧ (p1 ∧ p1)) ∧ p5)) → p5) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184895684305550256757523387477 : (((p5 → (False → p2)) ∧ ((p4 ∧ False) ∧ (p2 ∧ (p4 ∧ p1)))) ∨ ((((p4 ∧ False) → p1) ∧ (p1 ∧ ((p3 → p3) ∧ True))) ∨ (True ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248591664790555164833986375731 : ((p3 ∨ False) ∨ (((p5 → False) ∨ False) ∨ (p3 → (p4 ∨ (p3 ∨ (p4 ∨ ((p3 ∧ (False ∧ ((False ∧ (p2 ∨ (p2 ∧ p5))) ∨ p1))) ∨ p5))))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_681018014336900599449265268114 : (((((p3 ∧ True) → ((((False ∧ True) ∨ (p4 ∨ ((p5 ∧ ((True ∧ p2) ∨ p2)) → p3))) → p3) → p3)) → (((p2 → p3) ∧ True) ∨ True)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_172497149613756493368129696550 : (((p2 → (p4 ∧ (p4 ∧ p2))) → ((p2 ∨ False) ∧ ((p3 ∧ p3) → (True ∧ p1)))) ∨ (((p5 ∨ False) ∨ (p4 ∨ True)) ∨ (p4 ∧ (p3 ∨ False)))) := by
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
theorem thm_5_vars_119401770036589089896767877850 : ((p4 → ((((p1 ∨ (p2 → (p4 → ((False → p2) ∨ ((p1 ∨ (p5 → p1)) ∨ p4))))) ∨ (True → p4)) → (p5 ∨ p3)) ∨ p4)) ∨ (p4 ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_779393438700469515084434797140 : (((p2 ∨ (((((False ∧ ((((p1 → p2) → (p2 → True)) ∨ p4) ∨ True)) ∨ (p5 → p5)) → (p3 ∧ ((p3 ∧ False) ∧ False))) ∨ False) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147695265637099004284874280180 : ((((p4 → (p5 ∨ ((True → ((p4 ∧ p1) → p1)) ∨ (False ∧ False)))) ∧ ((False → p1) → (p2 ∧ p2))) → p3) ∨ (p2 ∨ (True ∨ (True → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234406362756971668533976130726 : ((p1 → (p4 → True)) → ((((((p5 ∨ p5) ∧ p3) → (p2 ∨ False)) ∧ False) ∨ (p4 ∨ ((p3 ∧ True) → ((p1 → (p1 → True)) ∧ True)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157023169627382790104402716913 : ((((p3 → False) ∧ (((p4 ∧ ((p2 ∨ p3) ∧ True)) ∨ p3) → ((p4 → p1) ∨ (p3 ∧ p5)))) ∨ False) ∨ ((((p5 ∧ False) ∧ p5) ∧ p3) → p1)) := by
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
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142400968593989446527291688195 : ((p4 ∧ ((p2 ∧ (p5 ∧ (((((p3 ∨ p2) ∧ p2) ∧ p2) ∨ p5) ∨ True))) ∧ (p5 ∧ (p4 → ((True → p4) ∧ p3))))) → (p1 ∨ (p3 ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Conjunctions on the left can always be decomposed.
      let h14 := h12.left
      let h15 := h12.right
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h5.left
        let h18 := h5.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h16
      case inr h19 =>
        -- Conjunctions on the left can always be decomposed.
        let h20 := h5.left
        let h21 := h5.right
        -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
        have h22 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h2
        -- We have shown the premise of h21, we can now drive its conclusion.
        let h23 := h21 h22
        -- We need to get the right conjuct of h23 based on <expert-advice>.
        let h24 := h23.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h24
    case inr h25 =>
      -- Conjunctions on the left can always be decomposed.
      let h26 := h5.left
      let h27 := h5.right
      -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
      have h28 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h27, we can now drive its conclusion.
      let h29 := h27 h28
      -- We need to get the right conjuct of h29 based on <expert-advice>.
      let h30 := h29.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h30
  case inr h31 =>
    -- Conjunctions on the left can always be decomposed.
    let h32 := h5.left
    let h33 := h5.right
    -- We want to use the implication h33 based on <expert-advice>. So we show its premise.
    have h34 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h33, we can now drive its conclusion.
    let h35 := h33 h34
    -- We need to get the right conjuct of h35 based on <expert-advice>.
    let h36 := h35.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h36



