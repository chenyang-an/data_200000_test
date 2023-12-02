variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305059532164939433496646485295 : (p1 ∨ (((p5 → ((p2 ∧ ((p4 → p5) → ((p2 ∨ p3) ∨ (True → True)))) → ((p1 → False) → (True → False)))) → p3) → ((True → p1) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693987537989621247555948633883 : (((((p1 → (((False ∨ False) → True) → (p4 → (p5 ∧ p2)))) ∨ (True ∧ p4)) ∨ ((p1 ∨ (((p4 ∧ p5) → True) ∨ (False ∧ p2))) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65005658767196946448757738743 : ((p2 ∨ ((False ∧ False) ∧ ((False ∨ (((p5 ∨ (p3 ∨ (p5 ∧ False))) → p2) ∧ (p2 ∨ p5))) ∧ ((p5 → False) ∧ ((p3 ∨ True) ∧ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612678955875198776164530319103 : ((((((((p3 → p1) ∧ p5) → (p5 ∨ ((False ∨ (False ∨ (p1 ∨ p2))) ∧ p2))) → (p2 → ((p3 ∧ False) ∧ False))) ∨ (p4 ∧ True)) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_69269566572511866078712733742 : ((p5 → ((p3 ∧ p3) ∨ ((p2 ∧ (p2 ∨ (False ∨ p1))) ∨ (((p5 ∨ (p5 ∨ (False → p2))) ∧ p1) ∨ (p2 → (p1 ∨ (False ∨ True))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43671161290828135172026837380 : (((((True → ((p1 ∧ ((False → (((p5 ∧ p2) → p2) ∧ False)) → p1)) → p4)) ∧ ((p2 ∨ (p4 → (p1 ∨ p2))) ∧ True)) → p4) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134660255263158951072864622757 : (((((p1 → ((p3 → (True → p4)) → (p4 ∧ p4))) → p2) ∨ ((p4 ∧ ((True ∨ False) ∨ p1)) ∧ (p3 → p2))) → p2) ∨ ((p1 → p2) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_87178572548981034020140663795 : (((p5 ∨ (((False ∧ p2) ∨ (p4 ∨ p4)) ∨ True)) → ((p3 → (False → p1)) → (p1 ∧ (((p1 ∧ p2) ∨ False) ∧ (True ∨ (True ∨ p5)))))) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 ∨ (((False ∧ p2) ∨ (p4 ∨ p4)) ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p3 → (False → p1)) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h6
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h4
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165337953016566211069651935021 : ((((((((p4 ∧ p1) ∨ p2) ∧ p1) → p4) → p3) → (p5 ∧ p2)) ∧ ((p4 ∨ p2) → p4)) ∨ (p3 → (((True ∧ p4) ∧ p4) → (p3 ∧ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the left can always be decomposed.
  let h7 := h2.left
  let h8 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h7.left
  let h10 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111766739279979905806006480207 : ((((((p5 ∧ p4) → p2) ∧ (True ∧ (((False ∨ ((p1 ∨ (p2 ∧ False)) ∧ p3)) → (True ∧ p1)) → p5))) ∧ (p1 ∨ p4)) ∨ True) ∨ (False → True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62420167366729567082274104784 : ((p3 ∧ (((True → (True ∨ p5)) ∧ (True ∧ p5)) → ((((p1 ∨ p1) ∧ p4) ∨ ((p3 ∧ False) ∨ (p3 ∧ p1))) ∨ (p3 → (p3 ∨ True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115231391536172999226670237726 : (((((p5 → ((p2 → p5) → (False ∨ p1))) → p2) ∨ p3) ∨ ((p2 → (p1 → False)) → (p3 → ((p3 ∧ (p5 ∨ p2)) → p3)))) ∨ (False ∧ p4)) := by
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
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_798053986224554738593424990837 : (((p1 → (((((p4 ∨ (((False → ((p1 ∧ True) ∧ p3)) ∨ p4) ∧ p3)) ∨ p4) ∨ p2) ∨ ((p2 ∨ False) ∨ p1)) ∨ (True → (p1 → p2)))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693160536142164624087278322381 : ((((p5 ∧ (p5 ∧ (((True ∧ p4) → ((p1 → p3) ∨ p3)) ∨ (True → True)))) ∧ ((p5 → (p1 ∧ ((False ∧ (p2 ∨ p3)) → False))) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40174593439083429038821540334 : ((((((p4 → (p3 ∧ (True ∧ p5))) ∧ p1) → ((((p1 ∧ p5) ∨ (((p2 → p2) ∨ (p5 ∧ p4)) ∨ p4)) ∨ True) ∧ p5)) ∧ p4) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134869714254229572181292303202 : (((p1 → ((((p2 ∨ ((p2 ∨ p2) → p4)) → p3) → ((p2 ∧ (p3 ∧ (p3 → False))) ∧ p2)) → (p2 ∨ p4))) → p5) ∨ (False → (p1 ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208771335696607358859837004534 : ((p2 ∧ ((p4 ∧ (p1 ∨ p5)) → p4)) → (((p1 ∨ (p2 ∨ p5)) → (p5 ∧ (p4 → True))) ∨ (((True → p1) ∨ (p4 → (p5 ∧ p5))) → True))) := by
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
theorem thm_5_vars_117671830856794319510758969118 : ((p3 ∧ (((p3 ∨ ((p1 → (False → p3)) → p2)) ∨ ((False ∨ p1) → False)) ∨ (p1 ∨ (((p5 ∧ p2) → (p3 ∨ p1)) ∨ p1)))) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180492020203712018535183428318 : ((((p5 ∨ (False ∧ (p5 → False))) ∨ (True ∨ p2)) ∧ (p3 → (p1 ∧ True))) → (((((True → ((True ∧ p2) ∧ False)) ∨ p2) ∨ p4) ∨ True) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- False on the left can always be used.
      apply False.elim h7
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
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
theorem thm_5_vars_124311714571951132096615956123 : ((((False ∨ (p3 ∧ True)) → ((False ∧ True) ∧ True)) ∧ (((False → p4) → (p5 ∧ p3)) ∧ ((p3 ∨ (p1 ∨ p3)) → (p2 ∧ p3)))) → (p5 → p2)) := by
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
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h7 : (False → p4) := by
    -- Implications on the right can always be decomposed.
    intro h8
    -- False on the left can always be used.
    apply False.elim h8
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h9 := h5 h7
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h11 : (p3 ∨ (p1 ∨ p3)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h10
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h12 := h6 h11
  -- We need to get the left conjuct of h12 based on <expert-advice>.
  let h13 := h12.left
  -- One of the premise coincides with the conclusion.
  exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114018760010992018646847540709 : ((((((False ∨ (((False ∧ p4) ∨ p4) ∨ (p5 ∧ False))) ∨ p5) ∨ (((p1 ∨ p4) → False) ∨ p1)) ∨ True) ∨ ((p3 ∨ p2) → p1)) ∨ (p1 ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110726575552572536977337558879 : ((((((((p3 → False) → ((p2 ∨ False) ∧ p4)) ∨ (((p4 → p5) → p3) ∧ True)) → p1) → ((p1 ∧ True) ∨ p5)) ∧ p5) ∧ False) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250722446056175611044151701961 : ((p1 → False) ∨ ((False ∨ True) → (((p2 ∧ p5) ∧ (((False → (p1 ∨ p5)) ∨ (p4 ∨ p3)) ∧ (p2 ∧ p2))) ∨ (p5 → (p5 ∨ (p5 ∧ p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310398497211247203803723019987 : (p2 ∨ (((p4 ∨ False) ∧ ((True → (False ∨ True)) ∨ True)) ∨ (True ∧ (p2 → (p3 → ((((p1 → False) ∧ False) ∨ p2) ∨ ((p2 ∨ p4) ∧ p1))))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41048495860046429548428788176 : ((((((False ∧ False) → p3) ∧ (((((True ∨ p5) → p3) → (p4 ∨ p3)) → p4) ∨ ((p1 → (p1 ∨ p5)) ∧ False))) → (p1 → p2)) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38166793980312214018956427953 : (((((p2 → (((p3 ∨ p4) ∧ (p1 ∨ p5)) ∨ ((p4 ∧ False) ∧ p2))) ∨ (p1 ∧ ((p3 ∧ p3) → p5))) ∨ (True ∨ (True ∨ p2))) ∧ True) ∨ False) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200552150313093900846742854852 : (((p2 → True) → (False ∨ ((p2 → p3) ∧ p5))) → ((((p3 → (p4 → False)) ∨ ((False ∨ ((p5 ∨ True) ∧ (p3 ∧ p4))) → p3)) → p4) → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((p3 → (p4 → False)) ∨ ((False ∨ ((p5 ∨ True) ∧ (p3 ∧ p4))) → p3)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h8.left
        let h11 := h8.right
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h8.left
        let h14 := h8.right
        -- One of the premise coincides with the conclusion.
        exact h13
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h15 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670151814117565922647722522179 : (((((((True → (p1 ∧ False)) ∨ p4) → False) → (((p3 → p2) ∨ p1) ∨ (p4 → (p5 ∧ ((p2 ∨ True) ∧ p4))))) ∨ ((False → False) → True)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_345698353816554178649668606903 : (p3 → ((True → ((p1 → (p2 → ((((p2 ∧ (False → p4)) ∨ p5) ∨ False) → ((((True → p4) → (p4 → True)) ∨ True) → False)))) ∨ False)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185374930684955085143108601583 : ((p5 ∧ ((p2 → (((p3 → p4) → p1) ∧ (p3 ∧ p2))) → False)) ∨ ((((p5 → p5) ∨ p3) ∨ p1) ∨ (((p2 ∨ (p2 ∧ True)) ∧ p5) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133576027185157351908650134204 : (((((p5 → (p4 ∨ (((False → p3) ∨ p3) ∨ p2))) → ((p5 ∧ p1) → (p4 ∨ (True → (True → False))))) ∨ False) ∧ p2) ∨ (p5 ∨ (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_632899705025786153371049082316 : ((((((((p2 ∨ (False → p1)) → ((p5 ∨ ((True → (p5 → p3)) ∧ (True ∧ p5))) → p3)) ∧ p5) ∨ (p5 ∨ p4)) ∧ (p1 → p3)) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_903126484379751851892754115356 : ((((p2 ∧ (((((p1 ∨ p5) → (False → (p4 ∨ p1))) ∨ p4) → False) ∧ ((p1 ∧ (p3 → p3)) ∨ False))) ∧ ((False ∧ (p4 → p3)) → p1)) → p4) ∧ True) := by
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
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h11 : (((p1 ∨ p5) → (False → (p4 ∨ p1))) ∨ p4) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h12
      -- Implications on the right can always be decomposed.
      intro h13
      -- False on the left can always be used.
      apply False.elim h13
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h14 := h6 h11
    -- False on the left can always be used.
    apply False.elim h14
  case inr h15 =>
    -- False on the left can always be used.
    apply False.elim h15
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185118925801034402505570377754 : (((True ∧ True) → (((p1 ∧ p1) ∨ p1) ∧ (p5 → (False ∨ p3)))) ∨ (((((False ∨ (p2 → p3)) → False) → (True ∨ p1)) ∧ (False → p4)) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_189792819982575500799027402294 : ((True → ((False ∨ ((p5 → p3) → False)) → (p2 ∨ True))) ∧ ((((False → ((p1 ∨ p4) ∨ (False ∨ (False ∨ (p4 ∧ True))))) ∧ p2) → p5) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121192086567072153917257430581 : (((p5 ∨ ((True ∨ ((p1 → (p1 ∧ p2)) ∧ ((p1 ∧ ((p3 ∨ (p5 → p4)) ∧ p5)) ∨ (p4 → p1)))) → (p2 → p3))) ∨ p1) → (p4 → p4)) := by
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
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h5 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136953491351369549158955875307 : (((True ∧ p2) → (p3 ∨ ((((p1 → (p1 ∨ p4)) ∨ True) ∧ ((p5 ∨ ((False → (p2 ∨ p1)) ∧ p1)) ∨ False)) ∧ p5))) ∨ (False → (p4 ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346773276111466923715939344020 : (p3 → (((True ∧ (p2 ∨ (((((((False ∨ (p4 ∧ p5)) → p3) ∧ p5) ∨ p2) ∧ False) ∨ p3) → p4))) → p5) ∨ (((p1 → True) ∨ p2) ∨ p2))) := by
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
theorem thm_5_vars_191573677178061006713513961978 : ((p2 ∧ ((True ∨ (p1 ∨ ((True ∧ p4) ∨ p3))) → False)) ∨ ((((p1 ∨ p2) → p3) ∨ (True ∨ ((True ∧ (p4 ∨ (p5 ∧ False))) ∧ p1))) ∨ p1)) := by
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
theorem thm_5_vars_50341479794557862765204484810 : ((((((p2 ∨ (True → p5)) ∨ False) → p5) ∨ ((p3 ∧ p3) ∧ ((((False ∨ True) → False) ∨ p3) ∨ p3))) ∨ (False ∨ (p4 → (p3 → p3)))) ∨ p3) := by
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
theorem thm_5_vars_712714275290002798757612533887 : (((((p5 → p2) ∧ (p1 → (p3 → p5))) ∨ ((((((p4 → p2) → p4) ∧ p4) → (False ∨ (p2 ∨ (False ∧ p5)))) ∨ (False → True)) ∨ True)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_41497758680270836403243387167 : ((((((p2 ∧ p3) ∧ (p2 ∨ (p3 ∨ p2))) ∨ (True → (p5 → p4))) → (((p5 ∧ False) ∨ ((p4 → p3) → (False ∨ p2))) ∧ True)) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_824612776732453028245260242320 : (((((p3 → (p4 → p4)) ∧ ((p5 → False) ∧ ((True ∧ p2) ∨ ((((p1 ∨ p4) ∧ ((p3 ∧ p4) → (p1 ∧ p4))) → p5) ∧ p3)))) ∧ p5) → False) ∧ True) := by
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
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h11 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h12 := h6 h11
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h16 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h17 := h6 h16
    -- False on the left can always be used.
    apply False.elim h17
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178338648941965496144416996341 : ((((p3 ∧ False) ∧ ((p5 ∧ False) ∨ ((False ∧ p3) ∨ False))) ∨ (p3 ∨ True)) ∨ (((p2 ∨ (True ∨ p1)) ∧ p4) ∨ ((p5 ∨ p1) ∨ (p4 ∧ True)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43256264706331758165880485900 : ((((p1 → ((((((True ∨ p4) ∧ p1) ∨ False) ∨ ((p1 → False) ∨ True)) ∧ p5) ∨ (p4 ∧ (p4 → (p2 ∨ (p1 → p2)))))) ∧ p4) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116273105967239943447006366610 : (((p5 ∧ (p3 ∨ False)) ∨ (p2 → ((((False ∨ (False ∧ ((p4 → p3) → p1))) → p1) → (p1 → (True → (True ∧ p1)))) ∨ True))) ∨ (p5 ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110981776323925776322295652528 : (((((((False → (p4 ∧ p1)) ∨ p3) ∨ (p2 ∨ False)) ∨ (((p5 ∨ False) ∧ ((p3 → p1) ∨ p3)) → False)) → (p5 ∧ p1)) ∧ p5) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255500281407552205784601010714 : ((p5 ∧ p2) → (((p1 ∨ p3) ∨ ((p5 ∨ (((((p5 ∨ ((p5 ∨ p1) ∧ True)) ∨ p4) → p3) ∧ p3) → p1)) → p3)) ∨ ((p2 → False) → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58015904168647008171364523593 : (((True ∧ p1) ∧ (p4 ∧ (((p2 ∨ ((True ∨ p2) ∧ False)) ∨ True) → ((((p3 → p2) ∧ (True ∧ p1)) ∧ (p1 → p5)) ∨ (p2 ∨ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197775196996506727700861530849 : (((False → (p3 ∨ p1)) ∧ (p3 ∨ (p4 → p1))) ∨ ((True ∧ p4) ∨ ((p5 → (p4 ∧ p4)) ∨ (((False → ((p3 ∨ False) ∧ p2)) → True) ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_611204639186774485355642823957 : ((((((False → (False ∧ p2)) → (p2 ∨ (p4 → ((p5 → False) ∨ ((True ∨ p4) → ((p1 ∨ (p2 ∧ (p5 → p1))) ∧ p1)))))) → False) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677838150341912596623737589355 : ((((((p5 ∧ p5) ∧ (((((True ∧ p5) ∧ p4) → p3) → p3) ∨ ((p1 ∧ True) ∧ p4))) ∧ (p2 → p4)) ∨ (p2 ∨ ((p3 ∧ True) ∨ True))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_674802525377856376238460216102 : ((((p4 → (p4 ∧ (p5 ∧ (p2 ∧ (((p4 ∧ ((p4 ∧ p2) ∧ p5)) ∧ (p2 ∧ p3)) ∨ ((p3 ∧ p2) ∧ p4)))))) → (p2 → (p4 → p3))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h14.left
    let h17 := h14.right
    -- Conjunctions on the left can always be decomposed.
    let h18 := h11.left
    let h19 := h11.right
    -- One of the premise coincides with the conclusion.
    exact h19
  case inr h20 =>
    -- Conjunctions on the left can always be decomposed.
    let h21 := h20.left
    let h22 := h20.right
    -- Conjunctions on the left can always be decomposed.
    let h23 := h21.left
    let h24 := h21.right
    -- One of the premise coincides with the conclusion.
    exact h23
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324001191038818680145013252970 : (p5 ∨ ((p2 ∧ ((((False ∧ False) ∧ p2) → (p3 ∨ ((p3 ∧ p2) ∨ p5))) ∧ True)) ∨ (((((p4 ∨ True) ∧ p4) → True) → (True ∧ p1)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311926672537111784507984615784 : (p2 ∨ (p3 ∨ ((((p4 → p5) ∨ (False → p4)) ∧ ((False → p3) → ((p5 ∨ p1) ∨ (p1 ∧ (((True → True) ∧ (p3 → True)) ∧ p1))))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_801818280369534251236000129171 : (((p2 → ((p2 ∨ (False → p1)) → ((p1 ∨ p4) → ((p2 → (p5 ∧ (p4 ∨ (p4 ∧ (p2 ∨ p1))))) ∨ (p2 → (False ∨ (p2 → p2))))))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h16
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h17
      -- One of the premise coincides with the conclusion.
      exact h17
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139668860912897672206260579624 : (((((True ∨ p5) ∧ p2) ∧ ((((p2 ∧ p4) ∨ p4) → ((((True ∧ p3) ∧ p4) → (p5 ∨ p3)) → True)) → p1)) → True) → (p1 ∨ (False ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_597012673535929549477249528354 : (((((((p3 → (False ∨ True)) → False) → p4) → (((p2 ∨ False) ∨ p4) ∨ ((True ∨ True) ∧ (True → (False ∨ ((True ∨ p3) ∨ p1)))))) ∧ True) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
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
theorem thm_5_vars_159675557991014145378521839104 : ((((p4 → ((p5 ∧ p4) → ((p2 ∨ (((False ∧ p4) ∧ p1) ∨ (False ∧ True))) → p5))) → p1) ∨ True) → (p3 ∨ (p5 ∨ (False ∨ (p5 → p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318553820980907205354027601744 : (p4 ∨ ((((((p3 ∨ (False → p5)) ∧ ((p5 → ((p5 → (p3 ∨ (p3 ∧ (p3 → p1)))) ∧ p4)) → False)) ∨ p5) ∨ True) ∨ p1) ∨ (True ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694184629445610578604406710724 : ((((((p2 ∧ False) → ((False ∧ p1) ∨ p3)) → ((p2 → p5) ∨ (p4 ∨ p5))) ∨ (p2 ∨ (True → ((True ∧ (p4 ∨ (p3 ∧ p3))) ∨ True)))) ∨ False) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_33588595117180748135599930780 : ((p4 ∨ (p2 ∨ (p2 → (p4 ∨ (p5 ∨ ((((p4 → (((p1 ∧ p4) ∧ p1) ∨ (p4 ∨ p2))) ∨ (p5 ∨ (p5 → p3))) ∨ p2) ∨ True)))))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225879915148698575031803201162 : (((p1 ∧ True) ∨ p3) ∨ (p5 ∨ ((p5 ∧ ((True → True) ∧ p3)) ∨ (((p1 → p3) → (p5 ∧ ((p2 ∨ p1) ∨ (False ∨ p2)))) → (p1 → True))))) := by
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
theorem thm_5_vars_147344144411682661046897633604 : ((((((p4 ∨ p5) → (p3 ∨ p5)) ∧ ((((False ∨ (False ∨ p3)) ∨ p5) → p4) ∨ False)) → (False ∧ p3)) ∨ True) ∨ (False → (False ∧ (False → p4)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181578814876813763974961978786 : ((p1 → (((True ∨ p1) → (False → ((p1 ∨ False) ∨ (p5 ∨ False)))) ∨ True)) → (((p4 → (False ∧ True)) ∧ (((p4 ∧ p5) ∨ p4) ∧ p4)) → False)) := by
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
  cases h5
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h10 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h11 := h3 h10
    -- We need to get the left conjuct of h11 based on <expert-advice>.
    let h12 := h11.left
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h14 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h15 := h3 h14
    -- We need to get the left conjuct of h15 based on <expert-advice>.
    let h16 := h15.left
    -- False on the left can always be used.
    apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608939206008604823862989588060 : ((((((((p2 ∧ ((False ∨ ((p2 → p3) ∨ p2)) ∧ p5)) ∨ True) ∧ p4) ∧ (((p3 ∧ (True → (p2 ∨ p5))) ∨ p3) ∧ p4)) ∨ p4) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206991449159916659955739371678 : ((((p3 ∨ p2) ∧ (p2 ∧ p1)) ∧ True) → (((((((p5 ∨ True) → p2) ∧ p3) ∧ (p3 → (p5 ∧ False))) ∨ p4) → p4) ∨ ((False ∧ False) ∧ True))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h9
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Conjunctions on the left can always be decomposed.
      let h13 := h11.left
      let h14 := h11.right
      -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
      have h15 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h14
      -- We have shown the premise of h12, we can now drive its conclusion.
      let h16 := h12 h15
      -- We need to get the right conjuct of h16 based on <expert-advice>.
      let h17 := h16.right
      -- False on the left can always be used.
      apply False.elim h17
    case inr h18 =>
      -- One of the premise coincides with the conclusion.
      exact h18
  case inr h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h5.left
    let h21 := h5.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h22
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h23 =>
      -- Conjunctions on the left can always be decomposed.
      let h24 := h23.left
      let h25 := h23.right
      -- Conjunctions on the left can always be decomposed.
      let h26 := h24.left
      let h27 := h24.right
      -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
      have h28 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h27
      -- We have shown the premise of h25, we can now drive its conclusion.
      let h29 := h25 h28
      -- We need to get the right conjuct of h29 based on <expert-advice>.
      let h30 := h29.right
      -- False on the left can always be used.
      apply False.elim h30
    case inr h31 =>
      -- One of the premise coincides with the conclusion.
      exact h31



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_189753220701193304150024171401 : ((p5 ∨ (((((p1 ∨ False) → p1) ∧ False) ∧ True) → p1)) ∧ ((p4 ∧ (((p1 ∧ p3) → p4) → (False ∨ ((p3 ∨ False) ∧ p5)))) ∨ (p1 ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118278467691797870486939299056 : ((p1 ∨ (((p3 → p4) ∧ p3) ∨ ((((p5 ∧ ((False ∨ False) ∨ ((False ∧ p5) ∨ p5))) ∨ p3) → (False ∨ False)) ∨ (False ∨ True)))) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315316360119519219285126121334 : (p3 ∨ ((p1 → (p5 ∧ (p4 ∧ p2))) → (((True ∧ (p4 ∨ False)) ∨ True) ∨ (((p2 ∧ (p1 ∨ p4)) → (p2 ∨ ((p2 ∧ p2) ∧ p2))) ∧ p3)))) := by
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
theorem thm_5_vars_651982538671754233310468351117 : ((((True ∧ (((p2 ∨ ((p5 → p4) → p5)) ∧ p5) ∧ ((p3 → ((p4 → (((p2 ∨ p1) → True) ∨ p2)) ∧ p4)) ∨ False))) ∧ (p5 ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354772398717946237057784045095 : (p5 → (((p1 ∧ ((p1 ∧ p2) ∨ (p1 → ((p3 ∧ p3) ∨ p1)))) ∧ (False ∧ ((p4 ∧ (p4 ∧ (p1 → (p2 ∨ p5)))) ∧ (p3 ∨ p3)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135350722654595893876056537112 : (((p5 ∧ (((True → (p2 ∨ p3)) → (p3 → ((p3 ∧ p3) ∧ (p5 ∧ p3)))) ∧ (p5 ∧ p4))) ∧ (False ∧ (p2 ∧ p5))) ∨ ((False ∧ True) → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225867672906562985695679826381 : (((False ∧ p4) ∨ p2) ∨ ((p1 → True) ∧ (False ∨ (p2 ∨ ((p3 ∨ (True ∨ (p4 ∨ (p5 → (p2 → p1))))) ∨ ((False ∧ (p4 → p4)) ∧ p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_647828761398329443573618379003 : ((((((((False ∧ ((p3 ∧ (p4 ∨ (p2 ∨ (p3 ∨ p3)))) ∧ p5)) ∧ (p5 ∨ ((p3 ∨ True) ∧ p5))) ∧ True) ∨ p1) ∧ p5) ∧ (p1 ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185941740017623434103168103172 : ((((True → p3) ∧ (False ∨ ((True ∧ p4) ∧ (p4 → False)))) ∧ p3) → ((p1 ∧ p5) ∨ ((((p3 → (p5 → False)) ∨ (False ∨ p2)) ∧ p2) ∧ p5))) := by
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
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h12 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h11
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h13 := h9 h12
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215409655027133069663191999805 : ((p2 ∧ (p2 → (p2 ∨ p1))) ∨ ((p3 → (((True → ((p4 ∧ (p2 ∨ (p5 → p1))) → p4)) → p4) ∧ (True ∨ p5))) ∨ (False → (False ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161706947286230695452843137759 : ((p2 ∨ (p3 ∨ (((False → p2) ∧ (p3 ∨ (p4 ∧ (p4 ∨ (p2 ∨ ((p5 ∨ p4) → p2)))))) ∧ p3))) → (((p4 ∨ True) → (p2 ∨ p1)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h9.left
      let h12 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h17 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h10
        case inr h18 =>
          -- Disjunctions on the left can always be decomposed.
          cases h18
          case inl h19 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h10
          case inr h20 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219440272731105616126755488067 : ((p4 ∨ ((p3 ∧ p1) → p5)) → ((((((p5 → True) → p3) → p1) ∧ (((p4 ∨ p1) → (p5 ∧ False)) ∧ p4)) ∧ (p1 → (p2 ∧ p4))) → p5)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h9 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h10 : (p4 ∨ p1) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h11 := h7 h10
    -- We need to get the left conjuct of h11 based on <expert-advice>.
    let h12 := h11.left
    -- One of the premise coincides with the conclusion.
    exact h12
  case inr h13 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h14 : (p4 ∨ p1) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h15 := h7 h14
    -- We need to get the left conjuct of h15 based on <expert-advice>.
    let h16 := h15.left
    -- One of the premise coincides with the conclusion.
    exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351230123677978805838125215113 : (p4 → (((p1 ∨ (((False ∨ p3) ∨ ((True ∨ p1) → ((p1 → p5) ∨ p5))) ∧ (p3 ∧ p5))) ∧ ((p1 ∨ p5) ∨ p5)) ∨ ((False → True) → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_79604946617874930903097332247 : (((((False → ((p5 → p4) → p4)) ∧ p4) ∧ (((p2 ∧ (True ∨ p4)) ∧ p2) → (p2 ∨ (((p4 → p3) ∧ p5) ∨ True)))) ∨ (p4 ∧ p4)) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187196360756648036278692516060 : (((p1 ∨ p1) → (p3 ∧ ((False → (p3 ∨ p3)) ∨ (p3 ∧ p3)))) → (True → (((((p2 ∧ p1) → p3) → (False ∧ (p4 → p1))) ∧ p1) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : ((p2 ∧ p1) → p3) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h10 : (p1 ∨ p1) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h11 := h1 h10
    -- We need to get the left conjuct of h11 based on <expert-advice>.
    let h12 := h11.left
    -- One of the premise coincides with the conclusion.
    exact h12
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h13 := h4 h6
  -- We need to get the left conjuct of h13 based on <expert-advice>.
  let h14 := h13.left
  -- False on the left can always be used.
  apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185293784804984393932415091171 : ((p2 ∧ ((p3 → p5) ∧ (((p4 ∧ (False ∨ False)) ∨ p1) → p3))) ∨ ((((((p2 → p3) → False) ∨ False) → (p1 ∨ False)) → False) ∨ (p2 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232974048272531913520523328951 : ((p3 ∧ (p1 → p1)) → (((p2 ∧ (((p4 → ((False ∨ (p5 ∧ False)) ∨ (p4 → p4))) ∧ (p3 ∧ (p3 ∧ p5))) ∨ (p2 ∧ p2))) ∨ p4) ∨ True)) := by
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
theorem thm_5_vars_150264972678743722332227894746 : ((p3 → ((True ∨ p4) → (((p5 ∧ ((True ∧ p1) ∨ (True → p2))) ∧ p4) ∨ (((p5 → p3) ∨ False) → p3)))) ∨ (((p5 ∧ p1) ∨ p2) → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h6 =>
      -- False on the left can always be used.
      apply False.elim h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_762141802673064486421873215623 : (((p3 ∧ (((((p2 ∨ p4) ∧ p5) ∨ (((((False ∨ False) ∨ ((p4 ∧ True) → False)) ∨ p3) → p2) ∨ (True ∨ p3))) ∨ p2) ∨ (False → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190921523037090890356119929476 : ((((p4 → (p4 → False)) ∧ p5) ∧ (p1 ∨ (p5 ∨ p5))) ∨ ((p1 ∨ p3) → (((True ∧ False) → p2) → (((p3 ∧ p5) ∧ p5) ∨ (True ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156600446524171924259716421554 : ((((((p4 ∨ (p3 ∧ (((p5 ∨ (True ∨ p1)) ∧ p3) ∨ p3))) ∧ p5) → (p1 → p4)) ∧ p5) ∧ p1) ∨ (True ∨ ((True ∨ (False ∨ False)) → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352038172271523838979798005256 : (p4 → (((False ∨ p4) ∧ ((True ∨ p2) ∧ (p5 ∨ p5))) → (p5 → ((p2 ∨ (True ∧ (p1 ∧ (p1 ∧ False)))) ∨ (False → (p5 ∨ (p5 → p1))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h5.left
    let h9 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h12
        -- False on the left can always be used.
        apply False.elim h12
      case inr h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h14
        -- False on the left can always be used.
        apply False.elim h14
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h16 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h17 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338948334589092087746490940830 : (p1 → ((p5 ∨ p5) → ((p3 ∨ ((False → True) ∧ (((p2 ∨ p5) ∨ (p2 ∨ p3)) ∧ p4))) → (p1 ∧ (False ∨ ((True ∧ True) ∨ (p4 → p3))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h6 =>
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h2
        case inl h14 =>
          -- One of the premise coincides with the conclusion.
          exact h1
        case inr h15 =>
          -- One of the premise coincides with the conclusion.
          exact h1
      case inr h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h2
        case inl h17 =>
          -- One of the premise coincides with the conclusion.
          exact h1
        case inr h18 =>
          -- One of the premise coincides with the conclusion.
          exact h1
    case inr h19 =>
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h20 =>
        -- Disjunctions on the left can always be decomposed.
        cases h2
        case inl h21 =>
          -- One of the premise coincides with the conclusion.
          exact h1
        case inr h22 =>
          -- One of the premise coincides with the conclusion.
          exact h1
      case inr h23 =>
        -- Disjunctions on the left can always be decomposed.
        cases h2
        case inl h24 =>
          -- One of the premise coincides with the conclusion.
          exact h1
        case inr h25 =>
          -- One of the premise coincides with the conclusion.
          exact h1
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h26 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h27 =>
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
    case inr h28 =>
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
  case inr h29 =>
    -- Conjunctions on the left can always be decomposed.
    let h30 := h29.left
    let h31 := h29.right
    -- Conjunctions on the left can always be decomposed.
    let h32 := h31.left
    let h33 := h31.right
    -- Disjunctions on the left can always be decomposed.
    cases h32
    case inl h34 =>
      -- Disjunctions on the left can always be decomposed.
      cases h34
      case inl h35 =>
        -- Disjunctions on the left can always be decomposed.
        cases h2
        case inl h36 =>
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
        case inr h37 =>
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
      case inr h38 =>
        -- Disjunctions on the left can always be decomposed.
        cases h2
        case inl h39 =>
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
        case inr h40 =>
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
    case inr h41 =>
      -- Disjunctions on the left can always be decomposed.
      cases h41
      case inl h42 =>
        -- Disjunctions on the left can always be decomposed.
        cases h2
        case inl h43 =>
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
        case inr h44 =>
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
      case inr h45 =>
        -- Disjunctions on the left can always be decomposed.
        cases h2
        case inl h46 =>
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
        case inr h47 =>
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
theorem thm_5_vars_177937529493359665527352352558 : ((((p3 → (True ∧ (p3 ∧ p2))) → (p1 ∧ (p2 → (p3 ∧ False)))) ∨ True) ∨ (p5 → ((((((False ∨ p3) ∨ p1) ∨ p1) ∧ p1) → p5) ∧ p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122883458492762333449469798198 : ((((p5 → p5) ∧ (((False → (((p3 → p4) → True) → False)) ∨ (((True ∧ False) → p1) → p4)) → p2)) ∧ (p1 ∨ (p1 → p5))) → (p4 → p2)) := by
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
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h8 : ((False → (((p3 → p4) → True) → False)) ∨ (((True ∧ False) → p1) → p4)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h9
      -- Implications on the right can always be decomposed.
      intro h10
      -- False on the left can always be used.
      apply False.elim h9
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h11 := h6 h8
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h13 : ((False → (((p3 → p4) → True) → False)) ∨ (((True ∧ False) → p1) → p4)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h14
      -- Implications on the right can always be decomposed.
      intro h15
      -- False on the left can always be used.
      apply False.elim h14
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h16 := h6 h13
    -- One of the premise coincides with the conclusion.
    exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606718138146304698732484383194 : ((((((((((False ∧ p3) ∧ ((False ∨ p2) ∧ True)) ∧ True) ∨ (((p5 ∨ True) ∨ p4) → (False → p4))) → p3) ∨ (p2 ∨ True)) ∧ True) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64664248059296667747904786953 : ((p1 ∨ (p1 ∨ ((((p2 → p1) → (p3 ∨ ((p5 ∧ p4) → ((p1 ∨ p3) ∧ ((p2 ∨ p1) ∧ (p1 ∧ (p4 ∨ False))))))) → p1) ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328990471635277604236464871846 : (True → ((((p5 → p3) → p2) ∨ (p5 ∧ p4)) ∨ ((p4 ∧ p1) ∨ ((p3 ∨ (True → False)) → ((p3 ∧ (p1 ∨ True)) ∨ (p1 ∨ (p3 ∧ p4))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166048969869324137672274231963 : (((True ∧ p3) → (True ∧ ((p1 → (p4 ∧ (p1 ∨ (False → (p4 → False))))) → (p4 → p2)))) ∨ (True ∧ (((p3 → (p3 → p4)) ∨ True) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306455447176938134419586294283 : (p1 ∨ ((p3 ∨ p2) ∨ ((p3 → p5) → (((((p1 ∧ p5) ∨ ((p3 ∨ p4) ∨ (p4 ∨ (p2 ∨ p4)))) ∨ (True → p3)) ∧ (False ∧ p3)) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151067869767623219427690863965 : ((((((p5 ∧ ((((p3 → (True ∧ p2)) ∧ (p3 → False)) → p2) ∧ p3)) ∨ p2) ∨ (p5 ∧ True)) ∨ True) → p1) → (p2 → (p1 ∨ (p3 → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((((p5 ∧ ((((p3 → (True ∧ p2)) ∧ (p3 → False)) → p2) ∧ p3)) ∨ p2) ∨ (p5 ∧ True)) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49440970557273505573786961223 : (((((p4 ∧ (((p4 → (p1 ∧ p3)) → (p5 ∨ (p5 → p5))) ∧ p1)) ∧ (((p4 ∨ p2) ∧ p5) ∨ True)) ∨ False) → (p3 ∨ (p4 ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173301162273562780900872636116 : ((p1 → (((p3 ∨ p3) ∨ p5) ∧ (((False ∧ (p1 → p2)) ∨ (p5 ∨ p1)) ∧ p3))) ∨ ((((p3 ∨ p4) ∧ (p4 ∧ p5)) ∧ (p5 → p4)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



