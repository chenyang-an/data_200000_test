variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196682302841919241951776293037 : (((((True ∧ (True ∧ p3)) ∨ p5) ∨ p2) ∧ p1) ∨ (((p2 ∨ ((((((False ∨ False) → (p2 ∨ False)) ∧ True) ∧ p3) ∧ p4) ∨ p4)) ∨ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611913495800730227964133428 : ((((p3 ∨ p1) ∧ (((False → ((True → (p5 ∨ (p1 ∨ p5))) ∧ (p3 ∧ (p3 → p5)))) → (p1 → False)) ∨ p5)) ∧ (p2 ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_635657958416828942602296756754 : (((((p4 ∧ (True ∨ (((p4 → ((p3 ∨ p1) ∨ False)) ∧ p1) ∨ ((p1 ∨ (False ∧ p2)) ∨ True)))) ∨ (p3 ∧ (p3 ∧ (False → p3)))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44571680193329175941132249787 : ((((((p1 ∨ (p4 → p1)) ∨ (False ∧ p4)) ∧ False) ∨ (((True → (p2 ∧ p3)) → (p2 ∧ (p3 ∨ ((p2 → p2) ∨ p5)))) ∨ p1)) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264580218325782333183685593547 : (True ∧ ((p1 ∨ (False ∧ p5)) ∨ ((((((p5 → p4) ∨ (True ∧ p2)) → True) → (p3 ∨ p5)) ∨ (True → False)) ∨ (p3 → (True ∨ (p4 ∨ p2)))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251176533606918621710156738291 : ((p2 → p1) ∨ ((p4 → ((False ∨ (p3 → (p2 → True))) → (p4 → (((((p3 ∨ True) → False) ∨ (p2 ∧ p5)) ∨ (p4 ∨ True)) ∧ p4)))) ∨ p1)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200227330278050606800309598891 : ((((True ∧ p4) ∨ p3) → (False ∨ (p2 ∧ p2))) → ((((((p3 ∨ True) → False) ∨ False) → (((True ∨ (p5 ∨ p2)) ∨ p3) ∧ p2)) → False) → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((((p3 ∨ True) → False) ∨ False) → (((True ∨ (p5 ∨ p2)) ∨ p3) ∧ p2)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h7 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h8 : (p3 ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h9 := h7 h8
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h10
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h11 := h2 h3
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43994650237833028024345911689 : ((((((((False → False) → p1) ∧ ((p2 ∧ p4) ∧ ((p3 → p1) ∨ ((p1 ∧ (p4 → False)) → p3)))) → p5) → p2) → (False ∧ p5)) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64905879137519228456087222744 : ((p2 ∨ (((((p2 ∧ ((p3 ∨ p4) ∧ ((p2 → (True ∧ False)) → (p2 ∨ p4)))) → True) → p1) ∨ True) ∨ (p2 ∧ (p1 ∨ (True ∨ p5))))) ∨ p2) := by
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
theorem thm_5_vars_113907295311488066294538194416 : ((((p5 → ((p5 ∨ (True → p2)) → ((p2 ∧ (p5 ∧ (p5 ∨ (p3 ∨ (p1 → p3))))) → p2))) → False) ∧ ((p4 ∨ True) → False)) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249425918532059662518112700485 : ((p5 ∨ False) ∨ ((((((p2 → (p3 ∨ ((False → p4) ∧ p1))) ∨ (p4 ∨ ((p4 ∧ p4) ∨ p3))) ∧ False) ∨ False) ∨ True) ∧ (True ∨ (True ∧ p2)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112083002176749970527348487866 : ((((False ∨ p3) ∨ (p2 ∧ (((((True ∧ True) ∨ p2) → (p2 ∧ p5)) → p2) ∧ (p5 ∨ ((p4 ∧ (p4 ∨ p5)) ∨ p1))))) ∨ True) ∨ (p1 ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64405683544760139023887662637 : ((p1 ∨ (((False ∧ (p3 → ((p5 ∨ (p2 ∧ p4)) ∨ p2))) → ((p1 → ((p2 → p5) ∧ ((p2 ∨ p4) ∨ p2))) ∨ (True → p2))) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_625123101814077059925875875697 : ((((True → ((p3 ∧ (p1 ∨ ((((True ∧ True) → p1) ∧ ((True ∨ (p2 ∧ (False ∧ p2))) ∧ p1)) ∧ p1))) ∨ ((p4 → False) → True))) ∨ p3) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157074188758941958260141310983 : (((p1 ∨ (p2 ∧ ((((p4 → p2) → False) → True) → ((p5 → p2) ∨ (False ∧ (p3 → True)))))) ∨ True) ∨ (p3 → (p5 ∧ ((True ∧ p3) → False)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_734371299735283488086130422107 : ((((False ∨ p4) ∧ ((((p1 ∨ (((p4 ∧ p4) ∧ p3) ∧ (False ∧ p2))) → (True → p4)) → (p3 ∨ (((p3 ∨ p5) ∧ p4) ∧ p1))) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114244473866933256863836212057 : (((p2 ∨ (True → ((p4 ∨ ((p2 ∨ p3) → ((p4 ∨ ((p4 → (p4 → p1)) ∨ True)) ∨ p4))) ∨ p2))) → ((p5 → p5) → p5)) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228196692145517762703010464968 : ((p5 ∧ (p5 ∧ p3)) ∨ (p3 → (((False → True) → ((False ∨ p2) ∨ (((p2 → True) ∧ (p3 ∨ p4)) ∨ p1))) ∨ (((True ∨ False) → p2) ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50051745038735705099596129270 : ((((False ∨ False) ∧ ((False → (p3 → (p3 ∨ (False ∧ (False → p2))))) ∧ ((p4 ∨ (p5 ∨ p1)) ∧ p2))) ∧ ((False ∧ (p1 → True)) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197061011096015580913352911914 : ((((p3 → p4) ∨ (True → (p5 ∨ p2))) ∨ p2) ∨ ((p3 → (p2 ∧ (p3 ∧ (((p1 → (p5 ∧ p1)) → p4) ∧ p5)))) ∨ (p2 → (False → p4)))) := by
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
theorem thm_5_vars_178025293878891853435845278587 : (((p3 → ((((True → p1) ∧ p2) ∨ ((p4 ∨ True) → False)) ∧ False)) ∨ p3) ∨ ((False → (p4 → False)) ∧ ((((p5 ∧ p1) ∨ p3) → p5) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785618789002396500289860436400 : (((p4 ∨ ((((((p2 → (p4 ∨ (p3 ∨ p4))) ∧ p3) → (((p1 ∧ p1) → p1) ∧ (p5 ∨ False))) ∧ (p1 → (False ∨ p1))) ∨ p3) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44220119376519927651145964069 : (((((p5 ∨ ((p5 → (p3 ∨ ((p1 ∧ ((p3 ∧ (False ∧ False)) ∧ p1)) ∧ p2))) ∨ p3)) ∧ p2) ∨ (((False → p1) → p5) → p1)) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712379664453893006534104867012 : ((((((p2 → p5) ∧ p1) ∧ (p2 → p1)) ∨ ((((False ∧ (((p2 → p2) ∨ True) → p3)) → (p2 ∧ p4)) → p2) ∨ ((True ∧ True) ∨ False))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_756830262444799210922237951674 : (((p1 ∧ (((p1 ∨ ((p4 ∨ p2) ∧ (p4 ∧ False))) ∨ p3) ∧ ((p2 ∨ ((((p2 ∧ ((False ∧ False) ∧ p3)) ∧ p4) → p4) ∧ p2)) → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159045919258288252329619092172 : ((p5 ∨ ((p1 ∧ ((((p1 → p3) → False) → p5) → (((p3 ∧ (p1 ∨ p2)) ∧ p4) ∧ False))) ∨ False)) ∨ (True ∨ ((p2 → True) ∧ (p2 ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184567786368040536078663181864 : ((((p4 ∨ (p4 → p4)) → (False ∨ (p1 ∧ p5))) → (p5 ∧ p3)) ∨ ((p2 ∨ ((p1 → (p5 ∧ (p1 ∨ p2))) ∧ (p1 ∨ p5))) ∨ (True ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119134457213382984820614224242 : ((p1 → (p2 ∨ ((p1 ∧ p4) ∧ (False ∧ ((p3 ∧ (True → (((True → ((True ∨ p5) ∧ (p4 ∧ p1))) ∨ p3) ∧ p3))) ∨ False))))) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_646061821081364308982973795694 : ((((True → (p3 ∧ (((p2 → True) ∨ ((((p3 ∧ True) ∨ (p5 ∨ p5)) ∧ p1) → p1)) ∨ ((p2 ∨ True) ∧ ((True ∧ p1) ∧ p4))))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51231622273988749329862958665 : (((((p3 ∨ (p5 ∧ p2)) ∧ True) → ((p1 ∨ ((p1 → (p4 ∧ p2)) → (p3 → p2))) ∨ True)) ∨ ((p4 ∧ ((p2 → p3) ∧ p5)) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337955037317690566534534444982 : (p1 → (((False ∨ True) ∧ ((p3 → True) ∧ ((p2 ∨ (p2 → p3)) ∨ p5))) ∨ (((True ∨ p5) ∧ ((p5 → ((p1 → p2) ∨ p5)) → p2)) → p2))) := by
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
  cases h3
  case inl h5 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h6 : (p5 → ((p1 → p2) ∨ p5)) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h8 := h4 h6
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h10 : (p5 → ((p1 → p2) ∨ p5)) := by
      -- Implications on the right can always be decomposed.
      intro h11
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h11
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h12 := h4 h10
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191555514618474278758471532056 : ((p1 ∧ (p4 ∧ (((p2 → p2) ∧ (p5 ∨ False)) ∨ False))) ∨ ((p2 ∨ ((False ∧ False) → p5)) → (False → ((p5 ∧ p3) ∨ ((p2 ∧ p2) → p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133685445441435814818639871130 : (((((((((p5 → p3) ∧ ((p1 → (p4 ∨ False)) ∨ p1)) → False) ∧ p5) ∨ p2) ∧ p4) ∨ (p2 → (p2 ∨ p5))) ∧ False) ∨ ((True ∨ p2) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42309171576576529079011570107 : (((p2 ∧ ((((p1 ∧ False) ∧ (p5 ∨ p3)) ∧ (p1 ∧ p5)) ∧ (((p2 ∧ True) → (True → (p1 ∧ (p3 ∧ (p3 ∨ True))))) ∧ p5))) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227192893808367273659166431613 : (((True → p2) → False) ∨ ((((False → p1) ∧ (((p4 → p4) ∨ p5) ∧ ((((True ∧ p5) ∧ False) ∧ p4) ∧ p2))) ∨ False) ∨ (p5 → (p5 → True)))) := by
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
theorem thm_5_vars_742949450202331111789232292207 : ((((p3 → p5) ∨ ((True ∧ ((p4 ∨ (p2 ∧ ((p1 ∨ p2) ∨ p5))) → ((True ∧ (p4 ∧ ((True → True) ∨ p5))) ∧ (p5 → p1)))) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51939260652329433361068874833 : (((((p2 ∨ p1) ∧ (((p3 → False) ∧ p2) ∨ False)) ∨ ((True → (True ∨ False)) ∧ p2)) ∨ (p4 ∧ ((p5 ∨ False) ∧ (p5 → (p3 ∧ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257746945487442564867109378206 : ((p3 ∨ p4) → ((((p5 ∨ (p2 → (p1 ∨ (((p2 ∧ p3) → p1) → (p5 ∨ p3))))) → (p3 ∨ p1)) ∧ (p5 ∧ p1)) ∨ (p1 ∨ (p5 → True)))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160126158203614064404202227446 : ((((((p3 ∧ False) ∨ (((False → p4) ∧ (p5 ∨ p2)) → p4)) ∨ (p3 ∨ p3)) ∧ p2) ∧ (p2 ∨ True)) → (((p4 ∨ (p3 → p4)) ∧ p5) ∨ p2)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h18
      case inr h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165884017031229844284198172339 : ((((p5 ∨ p1) ∨ p2) → (p4 ∨ (False ∧ (p4 ∧ (p1 ∨ (((p4 ∨ True) ∨ p4) ∧ p3)))))) ∨ (((p5 ∨ False) → p5) ∨ ((p2 → p5) ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307728282864892505708736453026 : (p1 ∨ (p3 → (((((p5 ∨ (p2 → (True ∨ p2))) → (True ∧ p5)) ∧ p4) ∧ (((((False ∨ True) ∧ p3) ∨ p4) ∧ p2) → (p2 ∨ True))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244330739082888017090909330010 : ((False ∧ False) ∨ (((p4 ∨ ((p4 → (((p4 ∧ True) ∧ (p5 ∨ p1)) ∧ p3)) ∧ p1)) ∨ True) ∧ (((False ∧ False) → (p2 ∧ False)) ∨ (False → p1)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41525034142886746434614324814 : ((((p2 ∧ ((p2 ∨ p3) → ((p5 ∨ False) ∨ (p3 → p1)))) ∧ (p2 ∧ (p3 ∨ ((p5 ∧ (False ∧ True)) ∧ (p2 ∧ (p5 ∧ p5)))))) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171365802424791079949114133772 : (((((False ∨ p4) ∨ ((False ∧ p4) ∧ ((True → True) ∧ p3))) ∨ (p4 → p5)) ∧ False) ∨ ((p2 ∨ ((True ∨ p4) ∨ ((p1 ∧ p3) → p2))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50533433537901867449763190821 : ((((((p3 ∧ (((((False ∨ ((p2 ∨ p3) ∨ p1)) → p3) ∨ p2) ∨ False) ∨ p3)) ∨ p4) → p5) ∨ p4) → ((p5 → (p5 ∧ p3)) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63999089028594466747044535407 : ((False ∨ ((((((p5 ∧ p4) ∨ (p1 ∨ p5)) ∧ ((((False → p5) ∨ (p5 → p5)) ∨ False) ∨ (p3 ∧ p4))) ∨ p3) ∧ True) ∧ (p3 ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65823943680430185712187554920 : ((p4 ∨ ((((p2 ∨ False) ∨ p1) ∨ p1) ∧ (p3 ∨ ((((p4 → ((p1 ∧ False) ∧ ((p1 ∧ (True ∨ p5)) ∨ p5))) ∧ False) → True) → True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184497296147071126502112288112 : (((((p2 ∨ False) ∧ p3) ∨ (p4 ∨ (p4 ∨ p5))) ∨ (p3 ∧ p4)) ∨ ((((((p5 → p5) → False) → p5) → p5) → (p5 → True)) ∨ (p2 ∧ p2))) := by
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
theorem thm_5_vars_172980234102265207768397276022 : ((p4 ∧ (p3 ∨ ((((p2 → (p1 ∨ p4)) → p2) ∧ (False ∨ (p2 ∧ False))) ∧ False))) ∨ ((((p4 ∧ p3) ∨ (p1 ∧ p3)) ∧ p1) → (p1 ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323243183535969141066931739041 : (p5 ∨ (((p4 → False) ∧ (True ∧ (((p3 ∨ p2) ∨ (p4 ∨ ((((False ∧ p5) ∨ p3) → True) ∧ ((p5 ∧ p1) ∧ p5)))) ∨ p4))) ∨ (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_635685852502136180195377116197 : (((((False → ((p1 → ((p2 → (p4 ∧ (p1 ∨ p1))) ∧ (((p5 → p2) → True) ∧ p1))) ∧ p2)) ∨ (p2 → ((False → p3) ∨ p4))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113896621722127266412053196834 : (((((((p3 ∨ p5) ∨ (p5 → ((p2 → p4) ∧ (p1 ∨ p4)))) → ((p4 ∨ False) ∨ True)) ∨ p4) → p5) ∧ (p2 ∨ (True → p1))) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_144900596370806509771285190680 : ((((p5 → ((p2 ∨ ((p4 ∧ p1) ∨ (p1 ∧ p2))) ∧ (p3 ∧ True))) ∨ True) ∨ (((True ∨ p5) → p2) → p1)) ∧ (False → (True ∧ (p5 ∧ p5)))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46181972734084004251806131599 : (((((p4 ∨ p1) → ((p4 → (((p4 ∧ (p2 ∧ False)) ∧ (p2 ∧ (True ∨ (p4 ∨ p5)))) → p2)) ∧ (p5 ∨ p5))) → p2) ∧ (p2 → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608978447331054697582626094182 : ((((((((True → p3) ∨ True) ∧ ((True ∧ p3) ∨ (p1 ∧ (p3 ∨ False)))) → (p5 ∧ (p2 → (((False ∧ p1) ∧ p5) → p5)))) ∨ True) ∨ False) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_208064423079073604702837846917 : (((p4 ∨ (p5 ∧ p1)) ∨ (False ∨ False)) → (((True → True) → ((p3 ∧ p2) ∧ p1)) → ((p1 ∨ False) ∨ (p5 → ((p4 ∧ p3) → (p1 ∧ p3)))))) := by
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
      have h5 : (True → True) := by
        -- Implications on the right can always be decomposed.
        intro h6
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h7 := h2 h5
      -- We need to get the right conjuct of h7 based on <expert-advice>.
      let h8 := h7.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8
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
    cases h12
    case inl h13 =>
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- False on the left can always be used.
      apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185430164650772506237679675588 : ((False ∨ (((True ∨ (False → (p2 ∧ p2))) → (p1 ∨ p4)) ∨ True)) ∨ (p5 ∨ (((p4 ∧ True) → ((p5 → ((True → p5) ∨ p4)) ∧ p1)) ∨ False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187753532705552772369425425971 : ((p2 → (((False → p3) ∨ ((p3 → p1) → p4)) ∧ (p4 ∧ p2))) → (((((True ∧ ((p2 → True) ∨ p2)) → p3) → False) → (p1 → False)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_8764261055862284884222970575 : ((((((False ∨ ((p5 → True) → p1)) ∧ (((p1 ∨ (False ∨ (p1 → (p4 ∧ False)))) ∧ False) ∧ p4)) ∧ p3) ∨ (p2 → (p4 ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219576770939448374256298647472 : ((True → ((p4 ∨ p2) → p2)) → ((((True ∨ ((p5 → True) ∨ ((p3 ∧ p5) ∨ p1))) → (p4 ∧ (p3 ∨ False))) ∨ (p2 → p2)) ∨ (p2 → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166485458669865880157814338841 : ((p3 ∨ ((((p2 → (p4 ∨ (p1 ∧ False))) ∨ p4) → p2) ∨ (p5 ∧ ((p5 ∧ p1) ∧ p2)))) ∨ (p5 ∨ (p3 ∨ (p4 → ((False ∨ p4) ∨ p3))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678258793048871939776923655583 : (((((((p5 ∨ p3) ∨ ((p2 ∨ p4) → p3)) ∨ p3) ∧ (p4 ∨ ((p3 ∧ ((p1 → p5) ∧ p1)) ∧ p3))) ∨ ((True ∧ False) → (True ∨ p1))) ∨ False) ∧ True) := by
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
theorem thm_5_vars_165679128145678721358545096235 : ((((p1 → ((p2 ∨ True) ∨ p1)) ∨ p3) → (((p4 ∧ p5) ∨ p4) ∨ ((p4 ∧ p2) → p3))) ∨ ((True ∧ (False ∨ (False ∧ p4))) → (p5 ∨ p3))) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193550207629300790936656001274 : (((p3 ∧ p4) → (p4 ∧ ((p1 ∧ True) ∧ (p1 ∧ p5)))) → ((((True ∧ ((True → p1) ∧ (False → ((p4 → p4) ∨ p1)))) → p3) ∨ True) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712650525153630344136861153596 : (((((p4 ∧ False) ∧ ((True → p2) → p3)) ∨ ((True → p5) → ((p4 ∧ ((((p4 ∧ p4) → p3) ∨ (p4 ∨ p1)) ∨ p2)) ∧ (p4 ∨ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141156486655028695938791524550 : (((True ∧ (((False → p4) → False) ∧ True)) ∧ ((p2 → (False ∨ p4)) ∧ (p5 ∧ (((False → (False ∧ False)) ∨ True) ∧ p3)))) → ((p2 ∨ p3) → p1)) := by
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
    let h6 := h4.left
    let h7 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h5.left
    let h11 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h16 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h17 : (False → p4) := by
        -- Implications on the right can always be decomposed.
        intro h18
        -- False on the left can always be used.
        apply False.elim h18
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h19 := h8 h17
      -- False on the left can always be used.
      apply False.elim h19
    case inr h20 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h21 : (False → p4) := by
        -- Implications on the right can always be decomposed.
        intro h22
        -- False on the left can always be used.
        apply False.elim h22
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h23 := h8 h21
      -- False on the left can always be used.
      apply False.elim h23
  case inr h24 =>
    -- Conjunctions on the left can always be decomposed.
    let h25 := h1.left
    let h26 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h27 := h25.left
    let h28 := h25.right
    -- Conjunctions on the left can always be decomposed.
    let h29 := h28.left
    let h30 := h28.right
    -- Conjunctions on the left can always be decomposed.
    let h31 := h26.left
    let h32 := h26.right
    -- Conjunctions on the left can always be decomposed.
    let h33 := h32.left
    let h34 := h32.right
    -- Conjunctions on the left can always be decomposed.
    let h35 := h34.left
    let h36 := h34.right
    -- Disjunctions on the left can always be decomposed.
    cases h35
    case inl h37 =>
      -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
      have h38 : (False → p4) := by
        -- Implications on the right can always be decomposed.
        intro h39
        -- False on the left can always be used.
        apply False.elim h39
      -- We have shown the premise of h29, we can now drive its conclusion.
      let h40 := h29 h38
      -- False on the left can always be used.
      apply False.elim h40
    case inr h41 =>
      -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
      have h42 : (False → p4) := by
        -- Implications on the right can always be decomposed.
        intro h43
        -- False on the left can always be used.
        apply False.elim h43
      -- We have shown the premise of h29, we can now drive its conclusion.
      let h44 := h29 h42
      -- False on the left can always be used.
      apply False.elim h44



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785943389297213341609501686733 : (((p4 ∨ (((p5 → (((p5 ∨ ((False ∨ True) ∧ ((p4 ∨ p3) ∧ (p4 ∧ True)))) → (p3 ∨ (True ∧ False))) ∨ p3)) ∧ p2) ∨ (p1 ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53979058532014283904148184209 : ((((((p4 ∧ (p3 ∨ (p2 → p3))) ∨ p2) ∨ p4) ∨ p2) → ((True ∧ p5) → (p3 ∨ ((p5 ∧ (True ∧ False)) ∨ ((True ∧ True) → True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_660136179815263101999601074865 : (((((((p1 → (p2 → (p1 ∨ p2))) → (p4 → ((p1 ∧ True) ∨ p5))) ∨ ((p3 → (p2 ∧ False)) ∧ (p1 ∨ p5))) ∨ p1) → (True ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314840021896565028720069906260 : (p3 ∨ (((p4 ∨ p5) ∧ ((True → p5) ∧ (((p3 ∨ p3) ∨ p2) ∨ True))) ∨ (((((p2 ∧ p3) ∨ (p3 ∨ (p2 ∧ False))) → True) ∨ p4) ∨ False))) := by
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
theorem thm_5_vars_69208532401308482054798043216 : ((p5 → ((((p3 ∨ True) ∧ p4) → ((p5 → p3) ∧ p2)) ∨ (False ∨ (((False → (p4 → ((p2 ∧ (False ∨ p3)) ∧ False))) ∧ p1) → p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198161414700914158577456468074 : (((p1 ∨ True) → ((p5 ∨ (True ∧ p1)) ∧ False)) ∨ (((p4 ∧ p3) → (False ∨ p4)) ∨ (False ∧ ((p5 → (p4 ∨ True)) ∨ (p5 → (True ∧ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_186889029762137828462866314065 : (((True ∨ (p3 ∧ (p3 → p5))) → (p3 ∧ (p5 ∨ (p1 ∨ False)))) → ((((p4 ∧ True) ∧ p1) ∨ ((p3 → p4) ∧ ((p3 ∨ p4) ∧ p5))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783313697451460035101847868199 : (((p3 ∨ (((p1 → (True ∨ (((p3 ∧ (p4 → p4)) ∧ (p1 ∨ ((p4 ∧ p5) ∨ True))) → p3))) ∨ p4) → (p3 ∧ (False ∧ (p2 ∨ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52621927880851035215090866529 : ((((p3 ∨ (p2 ∧ p4)) ∨ (p1 ∧ ((p2 ∨ ((True ∨ p2) ∨ p3)) → False))) ∨ (((True → (p5 → p4)) ∨ False) → ((True ∨ True) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690589224442019158087138896505 : ((((((((p1 → ((p4 ∨ p5) → (p5 → (p2 → p4)))) → p1) → False) → p4) ∨ False) → (((p3 ∧ (p1 ∨ p1)) → p4) ∨ (p1 ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172596381601726995688194212647 : (((True ∧ (True ∨ False)) → ((((p1 → True) → (p1 ∨ (p3 ∨ p3))) ∧ p5) ∧ False)) ∨ ((True → ((p4 ∧ (p5 → p5)) ∧ (p4 ∨ True))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689573567345427644951821711500 : ((((((p4 → ((False ∧ p5) ∧ p1)) ∧ p4) ∧ (p3 ∨ (((p1 → p1) ∧ p3) → p1))) ∨ (p1 → (p2 ∨ (p3 ∨ (True ∨ (p3 ∨ p2)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116290951656978126854286776244 : (((p4 ∨ (p4 ∧ p3)) ∨ ((p4 ∨ (p2 ∧ ((p5 ∧ (((p4 ∧ (p3 → False)) → (p3 ∨ p5)) → True)) ∨ (p1 ∧ p3)))) ∨ True)) ∨ (p5 → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147268092086332746042581914264 : ((((((((False ∧ (p3 → True)) ∧ ((p3 ∧ False) ∧ (p1 ∨ p2))) → p4) ∧ p3) ∧ (False ∧ True)) ∨ p3) ∨ p2) ∨ (p5 ∨ ((False → p3) ∨ p4))) := by
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
theorem thm_5_vars_305332267293687939795927308865 : (p1 ∨ (((p3 ∨ ((((p4 → True) → (p1 → (p4 ∧ True))) ∧ p5) ∧ ((p4 ∧ p4) ∨ True))) → p1) → ((p3 → ((p2 ∨ p3) → p5)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159055878823423334790995512100 : ((p5 ∨ (((False → True) → (p3 ∨ (p3 ∧ ((p5 ∧ True) ∧ p5)))) ∧ (p3 → (True ∨ (p3 → p1))))) ∨ (p3 ∨ (((False ∨ False) ∧ False) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217540274125612771895426205622 : ((((p5 → p2) ∧ False) → True) → ((p5 ∧ p2) → (((p5 ∨ ((p4 ∧ p3) ∨ p2)) → (True → False)) → (p1 ∧ (p5 ∧ ((False ∨ p5) ∨ False)))))) := by
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
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h6 : (p5 ∨ ((p4 ∧ p3) ∨ p2)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h6
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h9 := h7 h8
  -- False on the left can always be used.
  apply False.elim h9
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h10 := h2.left
  let h11 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h10
  -- Conjunctions on the left can always be decomposed.
  let h12 := h2.left
  let h13 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257566992339456012138116689288 : ((p3 ∨ p1) → ((((((p3 ∧ p4) ∧ p1) ∨ ((True ∨ (True ∨ (False ∧ True))) ∨ p4)) → (p4 ∧ p2)) ∨ p4) ∨ ((p2 → (p4 ∨ True)) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299442904029527551709836649404 : (False ∨ ((p1 ∨ (False ∧ (((p5 → ((p3 ∨ (p1 → p5)) ∧ (p1 → True))) ∨ p1) ∧ (p2 ∨ (True → (p2 → (p5 → (p1 ∧ False)))))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607043963565690113919815619498 : ((((((((p4 ∧ p5) ∨ ((p5 ∨ p3) → ((False ∧ p3) ∨ p3))) ∨ p5) → (((p2 → (p4 ∧ (p1 ∨ p4))) ∧ True) → p4)) ∧ p2) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341718946648152789487862890954 : (p2 → (((p4 ∧ (True ∨ (((p1 ∨ p2) → True) ∨ False))) ∨ ((True → ((False → (False ∧ p4)) → False)) ∨ ((p2 → False) ∧ True))) ∨ (p3 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149998070626830743211786999582 : ((p4 ∨ (p4 → (p1 ∨ (((p3 → ((p1 → p4) ∨ True)) ∧ ((p2 ∨ p3) ∨ False)) → ((p4 → p3) ∨ p2))))) ∨ ((p3 ∨ p1) ∧ (p4 ∧ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41247979973977693523880268471 : ((((((p2 → (p2 ∨ ((True ∨ (p4 → p1)) ∨ ((p1 → (p4 → False)) → p2)))) ∧ p3) → p5) ∨ (((False → False) → p4) ∨ p2)) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50399811681130095572501894341 : ((((False → False) → ((p4 ∧ (p4 → ((True → (p1 ∨ (p2 → (p2 ∧ True)))) ∧ (p4 ∧ True)))) ∨ p1)) ∨ ((p1 ∨ True) → (p2 → p2))) ∨ False) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621263803901995981422123979047 : ((((True ∧ ((((p1 → (p3 → p4)) ∨ (((p4 ∧ p3) ∨ False) ∨ (p2 → (False ∧ True)))) ∨ (p5 ∨ p3)) ∨ (p1 ∨ (p5 ∨ False)))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749918426918827591631601250338 : (((True ∧ ((((True → p3) → (False ∧ ((p1 → ((p5 ∨ ((p1 ∨ ((False → p5) ∧ p2)) ∧ p5)) → (p3 → p3))) ∨ p3))) ∨ True) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_211472285443149895661772037231 : (((p1 ∧ False) → (False → p2)) ∧ ((p3 ∨ (p2 → p2)) → ((p5 ∧ ((True ∧ p2) ∨ (p3 → (True → (p4 ∧ (False ∧ False)))))) ∨ (p1 ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h3
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42426858979292768188332255242 : (((p5 ∧ ((((p5 ∧ False) → (p3 → (p4 → (p5 ∧ p5)))) ∧ True) → ((((p5 ∨ p5) ∧ p5) ∨ ((True ∧ p3) → p2)) ∨ True))) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121368682087768432665653870042 : ((((((p5 → (p5 ∧ ((False ∧ (p1 ∨ p2)) ∧ (((p1 ∧ ((p5 → p2) ∨ p2)) ∨ p2) → p1)))) ∧ p5) → False) ∨ p1) → p1) → (p1 ∧ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p5 → (p5 ∧ ((False ∧ (p1 ∨ p2)) ∧ (((p1 ∧ ((p5 → p2) ∨ p2)) ∨ p2) → p1)))) ∧ p5) → False) ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h6 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h7 := h4 h6
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- We need to get the left conjuct of h8 based on <expert-advice>.
    let h9 := h8.left
    -- We need to get the left conjuct of h9 based on <expert-advice>.
    let h10 := h9.left
    -- False on the left can always be used.
    apply False.elim h10
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h11 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h11
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h12 : ((((p5 → (p5 ∧ ((False ∧ (p1 ∨ p2)) ∧ (((p1 ∧ ((p5 → p2) ∨ p2)) ∨ p2) → p1)))) ∧ p5) → False) ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h13
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h16 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h15
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h17 := h14 h16
    -- We need to get the right conjuct of h17 based on <expert-advice>.
    let h18 := h17.right
    -- We need to get the left conjuct of h18 based on <expert-advice>.
    let h19 := h18.left
    -- We need to get the left conjuct of h19 based on <expert-advice>.
    let h20 := h19.left
    -- False on the left can always be used.
    apply False.elim h20
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h21 := h1 h12
  -- One of the premise coincides with the conclusion.
  exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_768533423713862810007684643054 : (((p5 ∧ ((p5 ∨ (p4 ∧ (p5 → (p3 → ((p5 ∧ (((p4 ∧ True) ∧ p1) ∧ p3)) → False))))) → ((p3 ∨ p2) ∧ (p3 ∨ (True ∨ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_664461697077436334305971725221 : ((((p4 ∨ ((p4 → (p3 ∨ ((((p1 → ((p2 ∨ p4) ∧ ((p3 ∧ False) → False))) → True) ∨ (p1 → p5)) → p1))) → p1)) → (p5 → p5)) ∨ False) ∧ True) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165798281973923970394771722245 : ((((p1 → p5) ∧ p3) ∧ (((((True → p5) ∧ p2) → (p1 ∨ p1)) → p3) ∨ (p4 → p1))) ∨ ((p3 → (p4 → (p3 → p3))) ∨ (p1 ∧ p4))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695741805811163226415182413384 : ((((((p2 ∧ True) ∨ True) ∧ ((p3 ∧ p4) ∧ (p3 → ((p3 ∧ p5) ∨ False)))) → (p2 ∧ ((p1 ∧ p1) ∨ (((p1 ∨ False) → p2) ∨ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774869549822301340473117966810 : (((False ∨ (((p1 ∨ p5) ∨ (p3 ∧ p1)) ∨ (((False ∨ p2) ∧ (((p2 → ((p1 ∨ p4) ∨ True)) ∧ p2) ∨ False)) → (p5 → (True ∨ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



