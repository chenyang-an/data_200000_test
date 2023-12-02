variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166101667406280169603358530624 : (((p2 → False) → ((p4 ∨ False) ∧ (p3 → ((((False → p1) ∧ True) → (True → False)) ∧ False)))) ∨ ((p2 → (p3 ∨ (p1 ∨ (p3 ∧ p4)))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39636259843876342933166881294 : (((p3 ∨ ((((((p1 ∧ p3) ∨ (True ∧ p3)) ∧ ((p3 ∧ p4) ∧ p4)) ∨ ((p2 → (p2 ∨ p2)) → (True ∧ True))) → p1) → p4)) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56277766112112932188884154843 : (((p4 → (p2 → (p2 → p5))) ∨ (((False ∧ ((p4 ∧ (p4 ∨ (p1 ∧ p4))) ∧ (p5 ∧ ((p3 ∧ True) ∨ False)))) ∨ p3) ∨ (True ∨ p3))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324293976350334056757452028141 : (p5 ∨ ((((False ∨ (True → False)) ∨ p4) ∨ (p1 → False)) → (((((True ∧ ((p3 → p5) ∨ True)) ∨ ((True ∧ p5) ∧ p1)) ∧ p4) ∧ p3) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
        -- False on the left can always be used.
        apply False.elim h4
      case inr h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214201124582783539660796500570 : ((((True → p2) → p4) → False) ∨ (((((p2 ∨ p5) → True) → p1) ∨ ((p3 → True) → p1)) ∨ (p2 → ((True ∧ (False ∧ (p3 → p1))) → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  let h5 := h4.left
  let h6 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327177229689041218465036202956 : (True → ((p1 ∨ ((((p2 ∨ (((p1 ∧ (p3 ∨ p4)) → (True → (False ∨ True))) ∧ p4)) ∧ (False → p4)) ∨ ((False ∨ False) → p2)) ∧ p5)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313925693556207782009772884791 : (p3 ∨ ((((False ∨ p2) ∧ (((((False ∧ p2) ∧ p2) ∧ (p4 ∧ p2)) → (p5 ∨ ((p2 ∧ p2) ∧ True))) ∧ (p1 ∧ True))) ∧ p5) ∨ (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622454987464042423869036767475 : ((((p3 ∧ ((True ∨ True) → (((p3 → False) → (((False → p4) → (p5 ∨ ((p4 ∨ False) ∨ (True ∨ (False ∧ p2))))) ∧ True)) ∨ False))) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179711265625656364451159824414 : ((((p3 ∨ ((p2 ∧ ((p1 ∧ p4) → (p5 ∨ p3))) → p5)) ∨ True) ∧ True) → ((((p2 → p5) ∨ p2) ∨ True) ∨ (p2 ∨ ((True ∨ p4) ∧ p2)))) := by
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
theorem thm_5_vars_352123232933902958877662029444 : (p4 → ((True → (p4 → ((False ∧ True) ∧ True))) ∨ (True → (((p3 ∧ p1) ∨ (p5 ∧ (p3 → p3))) ∨ (True ∧ (p3 ∨ (p3 → (p4 ∨ True)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177906668375323795383386974924 : ((((((((True ∧ p4) ∧ p3) ∨ p1) → p3) ∨ False) → (p3 → False)) ∨ p3) ∨ (((((p1 ∨ (p2 ∧ (p1 ∨ p4))) ∧ p2) ∧ p3) ∨ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159283432988914938593775150767 : ((p4 → ((p2 → ((False ∧ True) ∨ (p5 ∨ p5))) ∨ (((True → (p4 ∨ (p4 → p3))) → p2) ∧ p1))) ∨ (False → (True ∧ ((p4 ∧ p5) ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59075957815299820150978566346 : (((p5 ∧ p1) ∨ (((p1 ∨ ((p3 ∧ ((True ∨ p2) ∨ ((((p2 ∧ p4) → p1) ∨ False) ∨ True))) ∧ (False ∨ True))) ∨ p3) ∨ (False → False))) ∨ p1) := by
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
theorem thm_5_vars_8013049005931393142963229972 : ((((((((p4 ∨ (((False → ((p2 ∨ True) ∨ p5)) ∧ False) → (p2 → p2))) ∧ (True ∧ True)) ∧ p5) ∧ p5) ∧ (p1 ∧ p2)) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230537410679806131979477590343 : (((False → p1) ∧ p5) → (False ∨ ((p3 ∧ ((False ∧ p3) ∨ p3)) ∨ ((p1 ∨ p4) → (((p3 ∧ p3) ∧ ((p5 ∨ p5) → (p5 ∨ p4))) → p5))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h10 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h11 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157506627302712462112058331305 : (((True ∧ (p5 → (((p1 ∧ ((p3 ∧ True) ∨ (True ∧ True))) ∧ p2) ∧ (p4 → p2)))) ∨ (p4 → p3)) ∨ (p1 → (p5 ∨ ((p1 → p3) ∨ p1)))) := by
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
theorem thm_5_vars_261513308750294345419390375122 : ((p5 → p3) → (((p2 → (p1 → (p1 ∧ False))) ∧ (p2 ∨ (((p4 → p1) ∧ (((p4 ∨ p2) → p2) ∨ p4)) ∧ False))) → (p3 → (p1 → False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h8 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h9 := h5 h8
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h11 := h9 h10
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h14.left
    let h17 := h14.right
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h18 =>
      -- False on the left can always be used.
      apply False.elim h15
    case inr h19 =>
      -- False on the left can always be used.
      apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350968538080753750562576648125 : (p4 → (((((p3 ∨ p4) ∨ (p1 → p1)) ∨ False) → (((p1 ∨ (((p4 → False) ∧ p5) → False)) → False) ∧ (True → (p2 ∨ p4)))) ∨ (p2 ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_808334600353649598432868765786 : (((p4 → (False ∨ (((((True → p2) → ((((p2 ∧ p3) ∨ (p2 ∨ (p5 ∨ p5))) → (True ∨ p3)) ∧ True)) ∨ (p3 ∨ p2)) ∨ p2) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671237179583787359233664725276 : ((((p4 ∨ ((True → ((((p3 ∧ p5) ∨ False) → (p4 ∨ p4)) ∧ (((True → p1) → p3) ∨ p5))) ∨ (False ∨ p4))) ∨ ((p1 → True) ∨ True)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_767525784682064357572209616687 : (((p5 ∧ (((True ∨ ((((p3 → (p5 ∧ p2)) ∨ ((p4 ∨ p4) ∧ p3)) ∨ ((p3 ∧ (p4 → p2)) ∧ (p4 → p4))) ∧ p1)) → False) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_637074975212253794616963510892 : ((((((((p1 ∧ p3) ∨ p3) → (p1 ∨ (p5 ∧ (p4 ∧ p5)))) ∧ False) ∨ (p2 → (((p3 ∨ p3) ∨ False) → ((p4 ∧ p2) → p5)))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192366959638742512190738332837 : (((p3 → (p4 ∧ (((p4 → p2) ∨ p3) → p1))) ∧ True) → ((((p5 → ((p2 ∧ p5) → (p5 → p3))) ∨ p1) ∨ (p2 ∨ True)) ∨ (True → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113749615228085700707740085896 : ((((p2 ∧ (p5 ∨ ((((True ∨ True) ∧ True) ∧ p3) → p5))) ∧ (((True → p4) → ((True → p2) ∧ p3)) ∨ p5)) → (p3 ∧ p5)) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_130426835798510141986393053172 : ((((p2 ∨ ((((p5 → p1) → p4) → ((p3 ∧ False) ∧ p4)) ∧ ((p5 ∨ p5) → p2))) → p2) ∨ (True ∨ (p3 ∨ True))) ∧ (p3 → (p2 → p3))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192159090185787124746703506743 : (((((p4 ∨ (False ∧ p5)) ∨ (p5 ∨ p1)) ∧ p5) ∧ p5) → (p3 ∨ ((p2 → ((p4 ∨ p3) ∧ (p2 ∨ ((p5 ∧ p5) → (p4 → p2))))) ∨ p5))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- False on the left can always be used.
      apply False.elim h9
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55508702279488752092083320540 : ((((False → p1) ∧ (p3 → (p2 → False))) → ((p4 → p5) ∨ ((((p5 → ((False ∨ p2) ∧ False)) ∨ (True → True)) ∨ p1) ∨ (p5 ∨ True)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_691867824634611637814002419974 : ((((False → ((p5 ∨ (p2 → False)) ∧ (True ∨ (((True ∨ (p5 ∨ p5)) ∧ p1) ∨ p1)))) → (((p4 ∨ ((p4 → p5) → p5)) ∨ False) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248221565953216738414793340182 : ((p2 ∨ p1) ∨ (((p3 ∨ True) ∨ ((p4 ∧ True) ∧ (True → p1))) ∧ (p2 ∨ ((((False ∨ p2) ∨ (p2 ∨ (True ∧ (p4 → True)))) ∨ p3) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198885122330012085121895982997 : ((p2 → (p2 → ((False ∨ (p3 ∨ p5)) ∨ p5))) ∨ (p2 → (p5 ∨ (((p3 ∨ (p3 → ((p1 → p1) ∨ True))) ∧ p2) ∧ ((p1 ∨ p5) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191289774840199674413376549559 : (((True → True) ∧ ((False ∨ (p4 ∨ p4)) ∧ (p5 ∧ p5))) ∨ ((((p1 ∧ (p4 ∧ False)) ∧ (p4 ∧ True)) → p2) ∧ ((True ∨ p5) ∨ (False → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h7
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227525056068125288397102266527 : ((True ∧ (p5 ∨ False)) ∨ (p3 ∨ (((((p1 → ((p2 → p2) ∧ p4)) → (p3 ∨ False)) ∧ p4) → (p3 ∧ True)) ∨ (p5 ∧ ((p5 ∧ p3) ∨ p4))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p1 → ((p2 → p2) ∧ p4)) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h6
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h4
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38932280678372147955734185312 : (((((True → p1) ∨ p5) → (((True ∧ ((p1 ∧ p4) → ((((p4 → True) ∧ (p2 ∧ True)) ∨ False) ∧ p1))) → p5) → (p5 ∧ p1))) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319065336531932774979542676872 : (p4 ∨ ((True → (((False ∨ ((p1 ∨ p2) ∨ ((p5 ∨ p3) → ((p5 → p5) → True)))) ∧ p5) ∧ (p1 ∨ True))) ∨ ((p2 → p2) ∨ (p4 ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679305458439797901232074542380 : ((((p1 → (p4 ∨ (((p1 ∨ (p5 ∧ (((p1 → p5) → p4) ∧ (p4 ∨ False)))) ∧ p5) ∧ (p3 ∧ False)))) ∨ ((p2 ∧ (True ∨ p5)) → p2)) ∨ p1) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191450080654068751866951787044 : (((p1 → p2) → ((True → p3) ∧ (p3 ∧ (p4 ∧ False)))) ∨ (((p3 ∨ p3) ∧ (p4 ∧ (((p5 → p1) ∧ (p1 ∨ False)) ∧ p4))) → (p1 → p3))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h13 =>
      -- False on the left can always be used.
      apply False.elim h13
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h4.left
    let h16 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- Conjunctions on the left can always be decomposed.
    let h19 := h17.left
    let h20 := h17.right
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h21 =>
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h22 =>
      -- False on the left can always be used.
      apply False.elim h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159050559958102319792472485160 : ((p5 ∨ (((p3 → ((((p1 ∧ p3) ∨ (False ∨ p2)) ∨ (p5 ∧ p4)) ∨ True)) ∧ True) ∧ (p3 ∨ p5))) ∨ ((True ∨ (p3 → p2)) ∨ (p4 ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41684829842355346606369123771 : ((((p1 ∨ ((p4 ∨ (p4 ∧ p5)) ∨ p4)) ∨ ((((p4 ∨ True) ∧ p1) ∧ p1) → (p1 → (False ∨ ((p2 ∨ p1) ∨ (p2 → p2)))))) ∨ p2) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  cases h5
  case inl h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68561855261192043071311475107 : ((p4 → (((((p5 ∧ ((((((p5 ∧ p1) ∨ (p1 ∨ p2)) → True) ∨ False) → (True → p1)) ∧ p3)) ∧ p3) ∨ (p5 → True)) ∨ p3) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147491403047545676342680126124 : (((p5 ∧ (True ∧ (((False ∨ p2) → (p1 → True)) → ((p5 ∨ p2) ∧ ((True ∧ (p1 → p4)) ∧ p3))))) ∨ p1) ∨ ((p1 ∧ False) → (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_144532281749108888589144577320 : ((((((False ∧ False) ∧ p1) ∨ ((False → ((p3 ∧ (p4 ∧ p2)) ∧ p1)) → p5)) ∧ (True → p5)) ∨ (p2 → True)) ∧ ((p5 → (True ∨ p3)) ∨ p2)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134300455711950024634620895408 : ((((p5 ∨ p2) → ((((False ∧ (p3 ∧ (p5 ∧ False))) ∧ (p2 → (p4 ∧ (p3 ∨ False)))) ∧ (True → True)) ∨ p3)) ∨ False) ∨ (False → (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324177878904645264917469298158 : (p5 ∨ ((False ∧ (False ∧ (p3 ∨ (p5 → (False → (p5 → p4)))))) ∨ (((((True ∨ p2) → (False ∨ (p3 ∧ False))) ∨ False) → p3) ∧ (False → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : (True ∨ p2) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h4 := h2 h3
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- False on the left can always be used.
      apply False.elim h8
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  -- Implications on the right can always be decomposed.
  intro h10
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263456045040538520912628474303 : (True ∧ ((((p1 → (((p2 ∨ (p1 ∧ False)) ∨ False) ∨ (False → (p3 ∧ ((p3 ∧ False) ∨ p5))))) ∨ p1) → (p2 ∧ False)) → (p4 ∨ (True ∧ p1)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p1 → (((p2 ∨ (p1 ∧ False)) ∨ False) ∨ (False → (p3 ∧ ((p3 ∧ False) ∨ p5))))) ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h4
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_807194905474099010907254615749 : (((p4 → ((p4 → ((((p4 ∧ (False → (p5 → (p1 ∨ (False ∨ p3))))) ∧ p3) ∨ True) → False)) ∨ ((True → p3) ∨ (True ∧ (p4 → p4))))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_697167194125269815603283836936 : ((((((p1 → p2) ∨ True) ∧ ((p4 ∨ (p3 → p1)) ∨ (True ∨ p2))) ∧ ((p1 → p3) ∧ ((p2 ∧ p3) ∧ ((p5 → True) ∧ (p1 → p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124282000176666193738243470484 : ((((p3 ∨ ((p2 ∨ p5) → (True ∨ p1))) ∧ p4) ∧ ((True ∨ (p4 → p3)) → ((p4 ∧ ((p5 → p4) ∧ p2)) ∨ (True → p2)))) → (p1 ∨ p2)) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h7 : (True ∨ (p4 → p3)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h8 := h3 h7
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
      have h15 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h14, we can now drive its conclusion.
      let h16 := h14 h15
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h16
  case inr h17 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h18 : (True ∨ (p4 → p3)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h19 := h3 h18
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- Conjunctions on the left can always be decomposed.
      let h23 := h22.left
      let h24 := h22.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h24
    case inr h25 =>
      -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
      have h26 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h25, we can now drive its conclusion.
      let h27 := h25 h26
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248231076806590144508919629112 : ((p2 ∨ p1) ∨ ((p1 ∨ p3) ∨ (p1 ∨ ((((False ∧ p4) → p1) → False) → (p4 ∧ ((True ∨ (p3 ∨ p3)) ∨ (p3 ∧ ((False ∧ p3) ∧ True)))))))) := by
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False ∧ p4) → p1) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- False on the left can always be used.
  apply False.elim h6
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_98814487594929972664751182102 : ((True → ((((p3 → p1) ∨ ((True → p2) ∧ False)) ∨ (False → ((p5 ∧ (p5 ∨ (False → (p1 → (p3 ∨ True))))) ∨ (True ∧ p4)))) ∧ p4)) → p4) := by
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
theorem thm_5_vars_574965833307575944972320376241 : (((p2 → (((p4 → (p4 ∧ p5)) ∧ (p5 → (False ∨ p4))) ∨ ((((False ∧ p3) ∨ ((True ∧ False) ∧ False)) ∨ p2) ∧ (False → (True → p1))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150365063257430882896153688325 : ((p5 → (p1 ∨ ((True → ((p1 → (p5 → p5)) → ((p3 → False) ∨ (p4 → ((p5 → False) ∨ True))))) ∨ p5))) ∨ (True → ((p2 ∧ p1) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_645858313831235283431835889735 : ((((True → ((((((p2 → ((False ∧ True) ∨ p1)) ∧ p2) ∧ p4) → (True ∧ (True → p1))) → (((p1 ∨ False) ∨ p1) → p5)) ∧ True)) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348193502867226448461192588424 : (p3 → ((p5 ∨ p4) → ((((((False ∨ p1) ∧ p4) → p1) → (((p3 ∨ (p3 ∨ (p3 → True))) ∧ p5) ∧ (p1 ∨ False))) ∧ p2) → (p1 ∨ p5)))) := by
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
  cases h2
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h8 : (((False ∨ p1) ∧ p4) → p1) := by
      -- Implications on the right can always be decomposed.
      intro h9
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h12 =>
        -- False on the left can always be used.
        apply False.elim h12
      case inr h13 =>
        -- One of the premise coincides with the conclusion.
        exact h13
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h14 := h4 h8
    -- We need to get the left conjuct of h14 based on <expert-advice>.
    let h15 := h14.left
    -- We need to get the right conjuct of h15 based on <expert-advice>.
    let h16 := h15.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136490973106988642640867573757 : ((((p2 ∧ False) → p1) ∧ (p3 ∨ (False ∧ (False ∨ (p4 → (p3 ∧ ((p4 ∨ (p5 ∨ p3)) ∧ ((False → p3) → False)))))))) ∨ (p5 → (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_775434341826289088422617462408 : (((False ∨ (p2 ∧ (p2 → (p1 ∧ (p3 ∨ ((p4 → (p3 ∧ (p3 ∧ ((p2 ∨ (p3 → p5)) ∧ p5)))) ∧ (((p2 ∧ p1) → p3) → p1))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656739660139668156578575563431 : (((((((p3 ∧ p3) → False) → (False ∧ p3)) ∨ (p5 → (p3 ∨ (((p4 ∨ p1) → p3) ∨ (p3 ∧ ((p1 ∧ p1) ∨ p4)))))) ∨ (False → p3)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43435475645009381558914441362 : ((((((p5 → False) ∧ (p5 → p2)) → (((True ∧ ((True → ((p2 ∨ p2) → (p1 → p5))) ∧ (p2 ∧ False))) ∧ True) → p4)) ∨ p3) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229204451229774018428843649734 : ((True → (p2 → p5)) ∨ (((True → p5) ∨ (((p1 ∧ p4) ∨ (p3 ∨ (False ∧ p4))) ∧ p1)) → ((p4 ∨ (p3 ∨ p4)) ∨ (False ∨ (False → False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
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
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- False on the left can always be used.
        apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_757474934416064268058294753827 : (((p1 ∧ (False ∧ (((p4 → ((p5 ∨ (False ∧ (True ∧ True))) ∧ (p1 ∨ p4))) ∧ (((True ∨ p1) → (p3 ∨ p1)) ∧ p2)) ∧ (True ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263690661982529797850709512533 : (True ∧ (((((p2 ∧ False) → p2) ∧ (p2 ∨ ((True ∨ False) → (p2 ∧ (p5 ∧ p5))))) → (p5 → p1)) ∨ ((p3 → ((True ∨ False) → p3)) → True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40903595666497196423716500510 : (((((p5 → p4) → (((False → ((p5 ∨ (((p5 → p2) → p4) ∨ p1)) → (True ∨ (p1 ∧ p5)))) ∨ p5) → p1)) ∧ (True ∨ p1)) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613943358083024134785405838955 : ((((((p1 ∨ (((False → (p1 → (((True ∨ p1) ∨ p4) ∨ p2))) → p5) → p2)) ∧ ((p1 → p5) → p4)) ∨ (False → (p2 → p3))) ∨ p4) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_103060310202278425804027777515 : ((((p4 → ((True → p5) ∨ (True ∧ p2))) → (False ∧ (((p3 ∨ p2) ∧ (p4 ∧ p1)) ∧ (False ∨ ((p1 ∨ p4) ∧ True))))) ∨ True) ∧ (p2 → True)) := by
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
theorem thm_5_vars_141462329689524383406488392301 : (((True ∧ (True → False)) ∧ ((p5 ∧ (p4 → False)) → (p4 ∨ ((((p3 ∨ (p3 ∨ False)) ∧ p5) ∧ (p4 ∧ p2)) ∧ p2)))) → (p4 ∧ (p4 → p5))) := by
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
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- False on the left can always be used.
  apply False.elim h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- Conjunctions on the left can always be decomposed.
  let h9 := h1.left
  let h10 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h9.left
  let h12 := h9.right
  -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
  have h13 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h12, we can now drive its conclusion.
  let h14 := h12 h13
  -- False on the left can always be used.
  apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_734503144977407542262781355828 : ((((p1 ∨ False) ∧ ((p5 ∧ ((((False → p1) → p5) ∧ (True → p5)) → (p2 → True))) → (((p4 → (True → p3)) ∨ p1) ∨ (p5 → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158742041901082342078686562126 : ((p4 ∧ ((((p2 ∨ (p4 → p4)) → ((p4 ∨ (False ∨ p3)) ∨ p2)) ∧ ((False ∨ True) → p2)) ∧ p1)) ∨ (p1 → ((p2 ∨ p1) ∧ (p1 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47255394093865373018291619604 : ((((p1 ∧ (p2 → (p1 ∨ (True ∨ p1)))) ∨ ((p3 ∨ (p2 ∨ ((p5 → (p1 ∨ p5)) → False))) ∨ (p5 ∧ (True → True)))) ∨ (False → False)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158982138847122705887345324876 : ((p3 ∨ ((p2 ∧ (p2 → (p4 ∧ (False ∧ (False ∧ (p5 → p4)))))) → (p5 ∧ ((True ∧ p1) → p5)))) ∨ ((True ∨ (True ∨ (False ∧ False))) → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- False on the left can always be used.
  apply False.elim h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h1.left
  let h12 := h1.right
  -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
  have h13 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h11
  -- We have shown the premise of h12, we can now drive its conclusion.
  let h14 := h12 h13
  -- We need to get the right conjuct of h14 based on <expert-advice>.
  let h15 := h14.right
  -- We need to get the left conjuct of h15 based on <expert-advice>.
  let h16 := h15.left
  -- False on the left can always be used.
  apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40802237904462714925811117799 : ((((False ∨ (((True ∨ (p5 → (p4 → p4))) → (p2 ∧ (p2 ∨ (p2 ∨ p1)))) → (True ∧ (False → (p5 ∨ (p1 → p1)))))) → p2) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_591881158690003796253476899335 : ((((((p5 → ((p1 ∧ False) ∧ ((p3 ∨ (True → False)) ∧ p5))) → (((p3 ∧ (p4 ∨ (p4 ∨ p2))) ∨ p3) → False)) ∨ (p1 ∨ False)) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50881656665252025109621911388 : ((((((((True ∨ True) → p1) → (p5 ∨ (p5 ∧ (p5 ∨ p4)))) → True) ∨ (p2 → p1)) → p4) ∧ ((p5 → True) ∧ ((p2 ∧ p5) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45861346097655525034798075981 : (((p3 → (((True ∨ p3) → ((((p2 ∨ (True → ((False ∨ False) ∧ ((p2 ∧ p5) ∨ (p5 → True))))) ∧ p2) → p3) → p5)) ∨ p5)) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198206849879618312384072767018 : (((p4 → False) → ((p1 → p2) → (True ∧ p3))) ∨ ((p5 → (p5 → True)) ∧ ((p2 → ((p5 → p1) ∨ True)) ∧ (((p4 ∧ True) ∨ True) ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
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
theorem thm_5_vars_205288884095856356338056355209 : (((p2 ∧ (p3 ∧ False)) ∨ (False ∧ p3)) ∨ (True ∨ (((p4 → ((p3 ∨ p1) ∧ False)) ∧ p1) ∨ (False ∧ ((p2 ∨ False) ∨ (p2 ∨ (False ∧ p3))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51872742250761991798924753690 : (((((p4 → p2) → ((True ∨ (p1 → False)) → (p4 ∧ ((p4 → p3) ∨ p2)))) ∨ False) ∨ (((True ∨ p3) → p1) → (False → (False ∨ False)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134889192315803042022488994403 : (((p4 → ((True ∧ (((p2 ∧ (p3 ∧ p1)) ∧ True) ∨ (False ∨ p3))) → ((True → (True ∨ (p2 → p1))) ∧ True))) → p5) ∨ (True ∨ (False → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38899222424687141102110591129 : ((((True ∧ (p5 → False)) ∨ (p2 ∧ (p5 → ((True → (((p3 ∧ p5) ∨ (((p3 → p1) → p2) → p2)) → (p2 → False))) → False)))) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_32503092357377395549484175977 : ((p2 ∨ ((((((False ∨ (p2 → False)) ∧ (p5 ∧ p5)) → (p3 ∧ p5)) → ((p1 ∨ p3) → p4)) ∨ (p5 ∨ (True ∨ p4))) ∨ (True ∨ p5))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_626557888993934093927869083638 : ((((p4 → ((p1 ∨ ((p2 ∧ p5) → p4)) → (p5 ∨ (((p1 ∧ p5) ∧ (((p3 ∧ p5) → p5) ∨ (False ∧ p1))) ∨ (p4 → p1))))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_113418505643104522831817869425 : (((((p2 ∨ ((p4 → (True → True)) → p1)) ∧ ((p3 ∧ (True ∧ (True ∧ False))) → ((p4 ∧ p4) ∧ p5))) ∧ p2) ∨ (p2 ∨ True)) ∨ (p5 ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678533588154478507544329723060 : ((((((p2 → p1) → p2) ∨ (((False ∨ ((p3 ∨ True) → p3)) ∧ (p2 → p4)) ∨ (p4 ∨ (p5 ∨ True)))) ∨ ((False ∨ False) → (p5 ∧ True))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166519752803292678481218204850 : ((p4 ∨ (((p1 ∨ ((True → p4) → True)) → False) → ((False ∧ (False ∨ p2)) ∧ (False ∨ p3)))) ∨ ((p3 → True) ∨ (((p2 ∨ p5) ∨ False) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621839792942439057221968342428 : ((((p1 ∧ ((True ∧ (False ∧ (((p1 ∧ p4) → (True ∨ p2)) → (p5 ∨ True)))) ∧ (p4 ∧ (p5 ∨ ((False → p5) ∧ (p4 → p2)))))) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303938332300838218815580247016 : (p1 ∨ (((p4 ∨ ((p3 ∨ (p3 ∧ p4)) ∨ p4)) ∧ (p5 ∧ (p3 → ((False → ((p1 ∨ p2) → False)) → ((p4 → p3) ∨ (True → p5)))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47022854496404924208888518817 : ((((p4 ∨ (False → (p3 → (p3 → (((p3 → (p4 ∧ (True ∧ (p2 ∧ (p4 ∧ (p1 → False)))))) → p3) ∨ p4))))) → p3) ∨ (p3 ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51934493051829777402847500611 : (((((p5 → ((p2 ∨ (p3 → p2)) ∨ False)) ∧ p3) ∧ (p1 → ((p3 → p1) → p5))) ∨ (p4 → ((True ∨ (False → False)) → (p1 → True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677794042464709170859544413147 : (((((p4 → (((p4 → ((True ∧ p4) → p4)) → p3) ∨ ((False → ((p2 ∧ p3) ∧ p2)) ∨ p4))) → False) ∨ ((p2 ∨ True) → (p4 ∨ True))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136381251355535980199630165031 : ((((True ∧ False) ∨ (p2 → p4)) ∨ (((p3 ∨ ((((p4 → p5) → p3) → p4) ∨ p1)) ∨ ((False ∧ p4) ∧ p3)) ∨ p2)) ∨ (False → (p2 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259738073675331654530932824733 : ((p1 → p2) → ((False ∧ ((p3 ∧ True) ∧ (((p4 ∧ (False ∧ ((True → p5) ∨ p2))) ∨ (p1 ∧ p4)) ∨ (p4 ∧ ((p1 → p5) ∨ p4))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_75694506943811182706199135269 : (((((((True → (p2 ∨ ((p1 ∧ p4) ∧ (((p1 ∨ ((p2 ∧ p1) ∧ True)) ∨ p2) ∧ p1)))) ∨ p2) → (True ∧ p4)) → p3) ∨ True) → p4) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((True → (p2 ∨ ((p1 ∧ p4) ∧ (((p1 ∨ ((p2 ∧ p1) ∧ True)) ∨ p2) ∧ p1)))) ∨ p2) → (True ∧ p4)) → p3) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355857482568608423636322317888 : (p5 → (((p2 ∧ ((p4 → (((p5 → (p5 → p3)) ∨ False) ∨ p5)) ∨ (p5 ∨ p5))) → (p4 ∧ ((p5 ∧ p5) ∧ True))) ∨ (False → (True → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_675336184317098933211019133340 : ((((((((p1 ∧ (False → (p3 ∧ ((p5 → p2) → p4)))) ∧ (False ∨ (p2 → p5))) ∨ p5) → p5) → False) ∧ ((p1 ∨ (p1 ∧ True)) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136406072899952094695517131490 : (((p2 → ((p1 → p3) ∧ p4)) ∨ (((p4 ∨ (False ∨ (p2 ∨ True))) ∧ (((p5 → p2) ∨ True) → (True → False))) → p5)) ∨ ((p5 ∧ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47842350800357789724973375486 : ((((p5 ∧ ((p2 → (p3 ∧ (((((p5 → True) ∧ p4) ∨ False) → ((p4 ∧ p4) ∨ (p5 → p5))) → True))) ∧ p4)) → p2) → (p3 ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184990451654323897446945562583 : (((False ∧ p3) ∧ (p3 ∨ ((p3 ∧ p2) → (p5 ∧ (p1 ∨ True))))) ∨ ((((p3 ∧ p3) → (p4 ∨ (True ∨ True))) ∨ p4) ∨ ((p4 ∨ False) ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_113120442773500574658644964024 : (((False → (p5 → (((p3 ∧ (p3 ∨ (((p1 → p4) ∨ (p2 → p5)) ∧ p3))) ∨ (p3 ∧ p4)) ∧ (True ∧ (p3 → True))))) → p1) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44972709111744221247372808736 : ((((False → p3) ∧ ((p1 ∧ p1) → (((((p4 → True) ∧ p1) ∧ ((True ∨ p3) ∧ (False ∧ p3))) ∧ ((p3 ∨ p3) → p5)) ∨ p2))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138361095359949966302168732174 : ((p4 → ((p3 ∨ (((p5 ∧ (p5 → p5)) ∨ False) ∧ (((p1 → (False ∨ False)) ∧ p2) ∨ (p4 → p2)))) → (p1 ∧ False))) ∨ ((p3 → True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198609177136935385906273547654 : ((p2 ∨ ((p1 ∧ p1) ∨ (p4 ∧ (p3 → p1)))) ∨ ((((p5 ∧ False) ∨ p1) ∨ (p1 → p3)) → (p2 ∨ (p1 → (False → (False ∧ (p1 ∨ False))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      apply False.elim h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h8
      -- False on the left can always be used.
      apply False.elim h8
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h11
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609930047062186683346896176151 : (((((p4 → (((((p2 ∧ p1) → (True ∨ (p2 ∨ ((p5 ∨ p4) ∧ (False → (p5 ∨ p2)))))) → p4) → p3) → (p2 → p5))) ∨ True) ∨ p4) ∨ p3) ∧ True) := by
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



