variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117549315387153085464962810709 : ((p2 ∧ ((((((p3 ∨ p1) ∧ ((p5 ∧ p1) → False)) → (p1 ∨ True)) → False) ∨ p2) ∧ (False ∧ (p3 → (p5 ∨ (p2 → p2)))))) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135116667040817765820807727115 : ((((p4 ∧ p3) ∨ (((True ∨ (True ∧ p3)) ∧ p2) ∨ ((False ∧ p2) ∨ (((p5 ∧ p4) ∧ p3) → p1)))) ∨ (False ∨ True)) ∨ ((p1 → p2) ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_681022614450362529485141360877 : (((((p4 ∧ p2) → (p1 → (((((p2 ∨ p2) ∧ (False ∨ True)) → p3) ∨ p3) → (p2 ∧ (p2 ∧ False))))) → (((p1 ∧ p1) ∨ p1) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200235546531023824777081696055 : ((((True → p3) ∨ p3) → ((False → p1) ∨ p4)) → ((((p1 → p3) ∧ p4) ∨ True) ∨ (p4 ∧ ((False → False) ∧ ((p4 ∧ (True ∨ False)) ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230209414227245376761167103039 : (((True ∨ True) ∧ p3) → (((p4 ∨ True) ∧ (True → ((p5 ∧ p1) ∨ p2))) ∨ ((p2 ∧ (((p1 → (p5 ∧ p2)) → (True ∧ p5)) ∨ p3)) → True))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69201406912893591404488548911 : ((p5 → ((((((True → (True → p4)) ∧ p2) ∧ p4) → True) → True) → (((False → False) → False) ∨ (p2 ∨ ((True → (p3 ∨ p1)) ∨ True))))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256036871293747676925437705754 : ((True ∨ p4) → (((True → (((p2 ∧ (((((p2 → p4) → False) ∨ (p4 ∨ p3)) ∧ p4) ∨ (p5 ∨ p5))) ∧ False) ∧ p1)) ∨ (False ∧ p2)) → False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h4 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h5 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h6 := h3 h5
      -- We need to get the left conjuct of h6 based on <expert-advice>.
      let h7 := h6.left
      -- We need to get the right conjuct of h7 based on <expert-advice>.
      let h8 := h7.right
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h10 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h11 := h3 h10
      -- We need to get the left conjuct of h11 based on <expert-advice>.
      let h12 := h11.left
      -- We need to get the right conjuct of h12 based on <expert-advice>.
      let h13 := h12.right
      -- False on the left can always be used.
      apply False.elim h13
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42051537075805229330113537723 : ((((p1 ∨ p2) ∨ ((p2 ∧ p2) → (((p3 ∨ ((True ∧ p4) → ((((True ∨ False) ∨ p5) → (p3 ∧ p5)) → p5))) ∨ p5) ∨ False))) ∨ p2) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h8 : ((True ∨ False) ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h9 := h5 h8
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308418271749153575361975776790 : (p2 ∨ (((((False ∨ (((p2 ∨ p2) → (p5 → p2)) ∧ (p1 → ((((False ∧ p2) ∨ p4) ∨ p4) → p3)))) → p5) ∨ (p2 ∧ p2)) → p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54562495058605238685130167170 : (((p4 ∧ ((p2 → p3) ∧ (p2 ∧ (p3 ∧ p2)))) ∨ (((p5 ∧ p4) ∨ ((p3 ∨ False) ∨ (False ∨ (p3 ∨ p3)))) → ((True ∧ False) ∨ True))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
        -- False on the left can always be used.
        apply False.elim h8
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- False on the left can always be used.
        apply False.elim h10
      case inr h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_801769881981185433744229424434 : (((p2 → ((p5 ∧ (p1 ∧ p2)) ∨ ((False ∨ (p4 ∨ (True → (((p4 → ((p3 ∨ True) ∨ True)) ∨ p4) ∨ ((False ∧ p4) ∨ p4))))) ∨ True))) ∨ p3) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65577105525363765854713511830 : ((p3 ∨ (p5 → ((p1 ∧ (p2 ∨ (p3 ∧ ((p2 ∨ p1) → ((p5 ∨ p3) → (p2 ∨ (p4 ∨ (True → ((False → False) ∨ p4))))))))) → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172372767682806014670746883751 : (((p2 ∨ (p3 ∧ (p3 ∧ (p5 → p1)))) ∨ ((p1 ∨ (p2 ∧ (p5 → p5))) → p2)) ∨ ((False ∧ (((False ∧ True) → p2) ∧ (p3 ∨ p4))) → p1)) := by
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
theorem thm_5_vars_135482310629782005893645182919 : ((((True ∨ ((True → p4) → p2)) ∨ ((((((False ∧ p1) ∨ p1) → False) → p1) ∨ p4) ∧ p5)) → ((p3 → False) ∨ False)) ∨ (p2 → (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338222646957981243787660797585 : (p1 → ((((False ∧ False) ∨ (p2 → p2)) ∧ p3) ∨ (((((True ∧ p3) ∨ True) ∧ ((p3 ∨ (p5 ∨ ((True ∨ p2) ∧ p5))) → p3)) ∨ p5) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300902095804781919996106200947 : (False ∨ (((False ∨ (((p3 → False) ∧ (False ∨ True)) ∨ (p1 → (p3 ∧ p5)))) → False) → (((p3 → True) → p5) ∨ (((p4 ∧ p2) ∧ False) → p3)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670269886147890642341700065107 : ((((((p1 ∨ p5) → (True ∨ p3)) → (True → ((p2 → (p4 → True)) → (((p3 → (p1 ∧ p4)) ∧ False) ∧ p2)))) ∨ (False → (False ∧ p3))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336272751367960551027354106426 : (p1 → (((((p5 ∧ ((p4 → p5) ∨ ((False ∨ p1) ∧ p5))) → True) → p4) ∨ ((p5 ∨ (p4 ∧ ((p3 ∧ (p2 ∨ p3)) ∨ p2))) → p3)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185378394740337518884299411831 : ((p5 ∧ (((p5 → (p2 ∧ False)) ∧ p3) ∧ (p4 ∨ (False ∧ p1)))) ∨ ((((((p2 ∧ (p1 ∧ True)) → p1) → False) ∧ p5) ∧ (False → p2)) → p1)) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : ((p2 ∧ (p1 ∧ True)) → p1) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- One of the premise coincides with the conclusion.
    exact h10
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h12 := h4 h6
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657775510394803325761026076461 : ((((True ∧ ((p4 ∧ (p5 → True)) ∨ ((((p5 → ((p3 ∨ p1) ∨ (True → (p5 ∨ p1)))) ∨ p2) → (p2 ∧ p5)) ∧ p5))) ∨ (p2 ∨ True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_679053699779692533222101610561 : ((((False ∨ (p5 ∧ ((True → ((p3 ∨ (False ∨ ((False ∨ p1) ∧ (p1 → p1)))) ∨ (p4 → p4))) → p5))) ∨ (True ∧ ((p2 ∨ True) ∨ p2))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620109076600750162973739236366 : (((((False ∧ False) ∨ (((((p5 ∧ (True → True)) ∨ (p4 → (((p5 → (True → p3)) ∨ p5) ∨ p3))) ∨ p3) → (p5 → p3)) ∨ False)) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680593533230285967407061413103 : (((((((p1 ∧ (False ∧ p5)) ∨ (p2 ∨ True)) ∨ p4) → ((((False → (False ∧ p2)) ∨ p2) ∨ True) → False)) → (p4 ∨ (p1 ∧ (p1 ∧ p3)))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p1 ∧ (False ∧ p5)) ∨ (p2 ∨ True)) ∨ p4) := by
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
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (((False → (False ∧ p2)) ∨ p2) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619527009772869345899896932256 : (((((p4 → (p5 ∧ p4)) → (True → (((((p2 ∨ (True → p3)) → (p3 ∧ ((p5 ∨ p3) ∨ p5))) ∨ p3) ∧ (p3 → p1)) → p5))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_216647070038885872649656882461 : ((((False ∨ p1) ∨ False) ∧ p4) → (((((p4 ∨ (p5 ∧ ((p1 ∧ p2) → True))) ∧ (p3 ∨ ((p4 → p2) ∧ (False ∨ p3)))) → False) ∧ False) ∨ True)) := by
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
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138425520143033432369833648386 : ((p5 → ((True → ((p2 ∧ True) ∨ ((True ∨ p4) → (((p5 ∨ p2) ∧ ((p5 ∨ False) ∧ p4)) ∧ p3)))) ∨ (False ∨ True))) ∨ (p5 ∨ (True → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56229218654152939305868500998 : (((p4 ∨ ((p1 → p3) ∧ False)) ∨ (p5 ∨ ((True ∧ p3) ∨ ((((p3 ∨ (p1 ∧ (True ∧ (p4 → (False ∨ p4))))) → p1) → p2) ∨ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168373767996869444443702706105 : (((p4 ∨ False) ∨ (p3 ∨ (p3 ∨ ((p2 → (p4 → p3)) ∨ ((p2 ∨ False) ∨ (False ∨ p3)))))) → ((((p3 ∨ (True ∨ False)) ∨ p4) → p2) → p2)) := by
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
      have h5 : ((p3 ∨ (True ∨ False)) ∨ p4) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h6 := h2 h5
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h10 : ((p3 ∨ (True ∨ False)) ∨ p4) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h9
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h11 := h2 h10
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h14 : ((p3 ∨ (True ∨ False)) ∨ p4) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h13
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h15 := h2 h14
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h17 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h18 : ((p3 ∨ (True ∨ False)) ∨ p4) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h19 := h2 h18
          -- One of the premise coincides with the conclusion.
          exact h19
        case inr h20 =>
          -- Disjunctions on the left can always be decomposed.
          cases h20
          case inl h21 =>
            -- Disjunctions on the left can always be decomposed.
            cases h21
            case inl h22 =>
              -- One of the premise coincides with the conclusion.
              exact h22
            case inr h23 =>
              -- False on the left can always be used.
              apply False.elim h23
          case inr h24 =>
            -- Disjunctions on the left can always be decomposed.
            cases h24
            case inl h25 =>
              -- False on the left can always be used.
              apply False.elim h25
            case inr h26 =>
              -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
              have h27 : ((p3 ∨ (True ∨ False)) ∨ p4) := by
                -- Show the left disjunct based on <expert-advice>.
                apply Or.inl
                -- Show the left disjunct based on <expert-advice>.
                apply Or.inl
                -- One of the premise coincides with the conclusion.
                exact h26
              -- We have shown the premise of h2, we can now drive its conclusion.
              let h28 := h2 h27
              -- One of the premise coincides with the conclusion.
              exact h28



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44910110972595231995168830034 : ((((p1 → (p2 ∧ p1)) → (((False ∨ (p5 → p5)) ∨ ((p1 → p5) ∨ (True → (((p2 ∨ (p4 ∨ p2)) → p4) ∨ p2)))) ∧ p4)) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219322654676275659479047392392 : ((p2 ∨ (p2 ∧ (p1 → True))) → (p3 ∨ ((False ∨ (((False → False) ∧ p3) → (True ∧ ((True → p1) ∨ (True ∨ ((p2 → p1) ∨ True)))))) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137798347450381161483894614266 : ((p2 ∨ (p1 ∨ (p1 ∨ ((((p3 → p5) ∧ p2) → ((p5 ∨ False) ∨ ((p5 → p5) ∨ False))) ∨ (p4 → (p2 → True)))))) ∨ (False → (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175066043820794970680515394461 : ((p2 ∧ (p4 → (((p3 → (p1 → ((False ∧ p2) ∨ p3))) → p1) ∧ (p5 ∧ False)))) → ((p4 ∨ (((False ∨ p5) ∧ (p3 ∧ False)) ∨ p2)) ∨ p3)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115077653824144422318793447724 : (((True ∧ ((p2 ∧ p5) ∨ (p4 ∧ ((p1 ∨ True) → (p2 ∧ True))))) ∨ (p4 ∨ ((p5 ∧ p3) ∧ ((False → (False → p5)) ∧ p5)))) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_640682500906210725581059865536 : (((((p4 ∨ False) ∧ ((((p5 ∧ ((False ∧ (True → p5)) → ((p2 ∨ (p1 → True)) ∨ p4))) → (p1 → (p2 → p5))) → p1) → p3)) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187333827605409916691468196225 : ((p2 ∧ ((False → (p1 ∨ ((False → True) ∨ p1))) ∧ (True ∧ p2))) → ((((p2 → (p3 ∧ p4)) ∨ p3) ∨ False) → ((p3 ∧ (p5 → p5)) ∨ p5))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h11 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h10
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h12 := h4 h11
      -- We need to get the left conjuct of h12 based on <expert-advice>.
      let h13 := h12.left
      -- One of the premise coincides with the conclusion.
      exact h13
      -- Implications on the right can always be decomposed.
      intro h14
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h1.left
      let h17 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- Conjunctions on the left can always be decomposed.
      let h20 := h19.left
      let h21 := h19.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h15
      -- Implications on the right can always be decomposed.
      intro h22
      -- One of the premise coincides with the conclusion.
      exact h22
  case inr h23 =>
    -- False on the left can always be used.
    apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43129429187331592144250192569 : (((((p3 ∨ ((p1 → (True ∨ True)) ∧ ((p3 ∧ (False ∧ p3)) → p2))) ∨ (p3 ∧ (((p3 ∧ False) → True) ∧ (p1 ∧ False)))) ∧ p4) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209100547294028585939303073811 : ((p2 ∨ ((p5 → (False ∧ p3)) → p3)) → (((False → p3) → (p2 → (((((p5 ∨ p3) ∧ p1) → (p5 → True)) → False) ∧ p2))) ∨ (False → p2))) := by
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
theorem thm_5_vars_46994460070560584566484705731 : ((((((p1 ∧ True) → ((p5 → p2) ∨ (True ∧ False))) → (p3 ∧ ((p4 ∨ ((p5 ∧ (False ∧ p1)) ∨ p5)) ∧ p1))) → False) ∨ (p5 → p5)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749738043183078921033803903239 : (((True ∧ ((((((p1 ∨ (p4 ∨ (p3 ∧ p2))) → p3) ∨ False) ∨ p4) → ((((p5 ∨ (True ∧ p2)) ∨ p1) ∨ p5) ∨ (p4 → p1))) ∨ True)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254877966023885645904359816268 : ((p4 ∧ True) → ((((p3 ∨ p3) → ((((p4 → True) ∨ (p5 ∨ p5)) ∨ p2) → ((p2 ∨ p5) → p3))) → ((p2 → (p2 ∧ p5)) ∨ p4)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112428197836992185339413985859 : ((((((p5 ∨ ((p4 ∨ ((False → (p2 ∨ False)) ∧ p1)) ∨ (False ∨ ((False ∧ p3) ∨ (p2 ∧ p4))))) → p5) ∧ p4) ∨ False) → p2) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_688815314043223479681329987247 : ((((((((p3 ∨ (p1 → p3)) ∧ False) ∧ (p2 → ((False → True) → p2))) ∧ p5) ∧ True) ∨ (p1 ∧ (((p3 → p3) → (True ∨ p3)) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157440895526709165669936655951 : (((p2 ∨ (((True ∧ (p3 ∨ True)) → ((p1 ∨ p3) → p2)) ∨ (False ∨ (False → p1)))) ∧ (p3 ∨ True)) ∨ ((p1 ∨ False) → (True ∧ (p5 ∧ p2)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53338339119957655351912750251 : (((((p5 ∨ ((p3 ∨ p5) → p2)) ∧ ((False ∨ p3) ∨ p2)) ∧ p5) → ((p1 ∨ ((p1 ∧ p1) → (((p5 ∧ p1) ∨ False) → p2))) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137421185728798471747910320619 : ((p4 ∧ ((((False ∨ p5) → (True ∨ p4)) ∧ (p5 ∧ ((p2 ∧ p4) ∨ (((p5 → (p5 ∨ p2)) → p2) ∨ p5)))) ∨ p5)) ∨ (True ∨ (p3 ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46901096720929428504672793981 : (((((((p4 → (p2 ∧ ((((False → True) → p1) → True) → False))) ∨ ((True → p2) ∧ p2)) ∨ p3) ∨ (p3 → True)) ∨ False) ∨ (p5 ∧ p4)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_307667647312688904069657177527 : (p1 ∨ (p2 → ((((True ∨ (((p2 ∨ False) ∨ (p3 ∨ p2)) ∧ False)) ∨ p3) → ((False ∨ False) ∧ ((p5 ∧ p2) ∨ (p2 ∨ (p1 → p5))))) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198707718505823842724115710205 : ((p5 ∨ (((p3 → p1) → (True ∧ p5)) ∨ p5)) ∨ ((p2 ∧ False) → (p5 ∨ (((p5 ∨ (p5 ∨ ((p1 ∧ p4) ∧ p4))) → (True ∧ p1)) ∧ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657562391741876844603287239822 : (((((p4 → False) ∨ (((((p2 ∨ p3) ∧ p1) → ((p5 → False) ∧ p2)) ∨ p3) ∨ ((p1 ∧ (p4 ∨ False)) ∨ (p2 ∨ True)))) ∨ (p1 ∨ p3)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_684787871323057986940525109285 : (((((True → p2) ∨ (p1 ∧ ((((False ∧ p1) ∧ True) ∧ (((p5 ∧ p3) ∨ p5) ∨ True)) ∨ p4))) ∨ ((p4 ∧ True) ∨ ((p4 ∨ False) → True))) ∨ p2) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172129305113503366042756460727 : (((((p1 ∨ False) ∨ (p4 ∧ False)) ∨ (p3 ∨ (p5 ∧ p1))) ∧ ((p3 → p2) ∨ p4)) ∨ (p5 ∨ (((p1 → p5) ∨ p3) → ((p2 → p2) ∧ True)))) := by
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
theorem thm_5_vars_262049967793083536609262774495 : (True ∧ ((p4 ∨ ((p4 ∨ p1) ∨ ((True → (p3 → (p4 ∧ p5))) ∨ ((p5 → (p1 ∨ (p5 → p1))) → ((p3 → (False ∧ False)) ∨ True))))) ∧ True)) := by
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
theorem thm_5_vars_41125595344171192652045223304 : ((((((p3 ∨ (p5 → (p3 ∨ False))) ∧ (p3 ∧ (((p5 → p5) ∧ p2) → (p1 ∧ (p2 ∨ False))))) ∧ False) ∨ ((False ∧ p5) → True)) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254877044431838183586546554300 : ((p4 ∧ True) → (((p4 ∨ (p5 ∨ ((False ∨ p1) ∨ (p4 ∨ ((((p3 ∧ p5) → True) ∧ (((p3 ∨ False) ∨ p1) ∨ p1)) ∨ p3))))) → p2) ∨ p4)) := by
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
theorem thm_5_vars_115388297565694626336117272186 : ((((p3 ∧ p1) ∨ ((p1 ∨ (p2 ∨ False)) → False)) ∧ (((((p1 ∨ ((p3 ∨ p5) → True)) ∧ p1) → p4) ∨ (False ∧ p2)) → p1)) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214477487635982280646858206481 : (((False ∧ p5) ∧ (p1 ∨ False)) ∨ (p5 → (p5 → (((p5 ∨ False) → ((((p5 ∧ (p3 → p5)) → False) → p1) → p1)) ∨ (p5 → (p4 ∨ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324953889743820924306117225504 : (p5 ∨ ((p4 ∨ p3) ∨ ((p5 ∧ ((p4 → False) → ((p4 → False) ∧ (p1 ∨ p1)))) ∨ (True ∨ (True ∨ ((True ∨ ((p3 ∨ p3) ∨ True)) → p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41916968014364773071523096605 : (((((p4 → False) → p3) → ((((((((True → p1) ∧ p3) ∧ p5) → (p2 ∨ (p3 → False))) → (p3 ∧ p4)) ∧ True) ∨ p2) ∨ True)) ∨ p4) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65989166855257185747668219150 : ((p4 ∨ (p2 → (p1 → ((p4 → (((((p1 ∨ p4) ∨ p2) ∨ ((p4 ∧ False) → p5)) ∧ ((p1 ∨ (p2 ∨ False)) → p4)) ∨ p2)) → p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184000705479965708593702099539 : ((((((p3 ∨ (p4 → (p1 ∧ p4))) ∨ p1) ∧ p1) ∨ False) ∨ p2) ∨ ((True ∧ p4) → ((p5 ∨ p3) ∨ ((p4 ∨ p3) ∨ ((p2 → p4) ∧ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308660638614062904883144662322 : (p2 ∨ ((p3 ∧ ((p1 ∧ True) → ((((p4 ∨ p4) → (True → (p2 ∧ True))) → p3) ∨ ((p1 → (p2 ∧ False)) → ((p5 ∨ True) ∧ p4))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140163003112678530614435081937 : (((((False ∨ (p2 ∧ p3)) ∨ ((((p2 → p4) → (True → p4)) ∨ (False → False)) ∧ True)) ∨ (p1 ∧ p5)) → (False ∧ p5)) → ((True → True) → p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (((False ∨ (p2 ∧ p3)) ∨ ((((p2 → p4) → (True → p4)) ∨ (False → False)) ∧ True)) ∨ (p1 ∧ p5)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h3
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337135326900127264576302739183 : (p1 → ((p2 ∨ (((False ∨ (p1 ∨ p2)) → (p1 ∧ ((False → p5) → p2))) ∨ (((p1 ∧ False) ∨ (p2 ∧ (True ∨ p5))) ∨ p1))) ∨ (True → False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317756559442881181178032937978 : (p4 ∨ (((((p3 → (False ∧ (p5 → (((True → p3) → (p5 ∨ p5)) ∨ p3)))) ∨ True) ∧ p5) ∧ (False ∨ (((p2 ∧ p4) → True) ∧ p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217910737966275510082512229601 : (((p4 → (p1 ∨ True)) → False) → (p4 ∨ (p3 ∨ ((((True ∧ p2) ∧ (p1 ∨ (False → ((False → True) ∧ p2)))) → False) → ((p4 → p2) ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p4 → (p1 ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67620150846227668424010613450 : ((p1 → (p4 ∧ ((((True ∨ p5) → p1) ∨ True) → ((p2 ∧ (p5 ∧ ((p2 → p3) ∧ (p3 ∨ ((p3 ∨ (p1 ∨ True)) → p5))))) ∨ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187351770285039711191087472082 : ((p2 ∧ (p2 → ((p3 ∧ True) ∨ ((p1 ∧ p2) ∧ (False ∧ p3))))) → (((p5 → True) ∧ (False ∧ (((p3 ∨ p2) → False) ∧ (False ∨ p5)))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h11.left
    let h15 := h11.right
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53322649613558259155467677701 : (((p3 → (p5 ∨ (p4 ∨ ((p5 ∧ ((p2 → False) ∧ p3)) ∧ p2)))) ∨ (p4 → (True ∨ (False ∧ (False → (p4 ∨ ((p1 ∨ False) ∨ p1))))))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323667248021373317927272985627 : (p5 ∨ (((((p2 ∨ (p2 ∨ p5)) ∨ ((True → p3) → p3)) → False) ∧ ((p2 ∧ p4) → ((p2 ∨ True) ∨ True))) ∨ ((True → (p2 ∧ False)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111863771781793967289748818315 : ((((p4 ∧ (p4 ∧ (((p1 → (p4 → (p3 ∨ (p5 → (True ∨ False))))) ∨ p2) ∧ p4))) ∧ ((p3 → (False ∨ p1)) → p5)) ∨ True) ∨ (p3 ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52937142924016737681681531334 : ((((p2 ∨ (False ∧ (((p1 → p4) ∧ (p1 ∨ p4)) ∧ p4))) ∧ p1) ∧ ((True ∧ (((p2 ∧ p3) → False) ∨ (p5 ∧ p2))) ∨ (p5 ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354818531714386102781627485408 : (p5 → (((p1 → (p5 ∨ True)) ∧ (p1 ∧ ((((((p3 ∨ ((p5 ∧ False) ∨ (True ∨ (False ∧ p5)))) → True) ∨ p3) ∨ p4) → False) ∧ False))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164801865884805904095226043866 : (((((p3 → p4) → False) ∨ (p3 ∨ (((True ∧ False) → (p3 ∨ p3)) → (True → p2)))) ∨ True) ∨ (p4 → (((p1 → (p4 → False)) ∧ True) ∧ False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171898745246730398620196530322 : (((p5 ∨ ((((((p3 ∨ p4) ∧ (p5 → True)) → p5) → p2) → p1) ∨ p1)) → p5) ∨ (((p2 ∧ (True ∨ (True ∨ (p2 ∧ p2)))) ∧ False) → p5)) := by
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h3
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- False on the left can always be used.
      apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117500924798715182812521987310 : ((p2 ∧ (((p5 ∧ (False ∨ (p2 ∨ (((True ∨ True) ∧ False) ∧ ((p5 ∨ (p1 ∧ p5)) → (p2 ∨ p2)))))) ∧ (False → True)) ∧ True)) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342906498309561588834238826092 : (p2 → ((p1 ∧ ((p4 ∧ (p5 ∧ p5)) → p5)) → ((((p5 → ((p3 ∧ (True ∧ (p1 ∨ p1))) → (True ∧ p5))) → False) ∨ p3) ∨ (p3 → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_661375507625322661596993578829 : ((((((p5 ∧ p4) ∨ (p2 → (p2 ∧ ((p2 → (p1 → (((p2 ∨ p5) → (p5 → False)) ∧ p5))) ∧ p1)))) → (p3 ∨ p5)) → (True ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190398987378542422115456357222 : (((p3 ∧ (((p1 → p5) ∨ (p4 ∨ p1)) ∧ False)) ∨ False) ∨ ((((p1 → ((p5 → (p1 ∨ p2)) ∧ p4)) ∧ p2) → (p2 → (True → p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53176967221357125094930561978 : ((((((p5 → True) → p4) ∧ ((p4 ∨ p1) ∨ (p5 ∧ p1))) → False) ∨ (((True ∨ (p4 ∨ (p1 ∧ p4))) → False) → (p4 ∨ (p5 ∧ p2)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ (p4 ∨ (p1 ∧ p4))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117945750777326856108537471099 : ((p5 ∧ (p4 ∧ ((p5 ∨ False) ∧ (((p4 ∨ False) ∧ (((p1 → ((p1 → p2) → (p2 ∨ p4))) ∨ (p2 → p1)) → p5)) → False)))) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193095241189410914767179957197 : (((p4 ∧ (True → (p3 ∧ False))) ∧ (True → (p2 ∧ p4))) → (p3 ∧ (((((p3 → False) → True) ∨ p5) ∧ p5) ∧ (p2 ∨ ((True ∨ p5) ∨ True))))) := by
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
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- One of the premise coincides with the conclusion.
  exact h8
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h9 := h1.left
  let h10 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h9.left
  let h12 := h9.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h13
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h14 := h1.left
  let h15 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h16 := h14.left
  let h17 := h14.right
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
  -- Conjunctions on the left can always be decomposed.
  let h21 := h1.left
  let h22 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h23 := h21.left
  let h24 := h21.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_779818313321484153336227539400 : (((p2 ∨ (((True ∨ True) ∨ (((p2 → True) ∧ ((p3 → p2) → p2)) → (p1 ∨ (p3 → (p5 ∧ (p2 ∧ (p5 → (p1 ∧ p4)))))))) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216087836576575034772549863463 : ((True → ((True ∧ p3) ∨ p4)) ∨ (((p1 ∧ (p1 → (p5 ∨ False))) → (p2 ∨ p5)) ∨ (p3 ∧ ((((p3 → p2) → p1) → False) ∧ (p3 ∧ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205496551650520856317194421946 : (((p2 ∧ p2) ∧ ((p5 ∧ True) ∧ True)) ∨ (p4 → ((((p4 ∧ True) → p4) → (((p5 ∨ (p5 ∨ (False → p1))) ∨ p1) → p1)) ∨ (False → False)))) := by
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
theorem thm_5_vars_147525741766737461689043577505 : (((True → ((p3 ∧ (((p2 ∧ (p4 ∧ (p1 ∧ p5))) ∧ p5) → p2)) ∧ ((p4 → p2) → (False ∧ p4)))) ∨ True) ∨ ((p4 → (p2 ∧ p1)) → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254220586086859927075511314883 : ((p2 ∧ p2) → (((p4 ∧ ((p5 → ((p3 ∧ (((p5 → ((p4 → p4) ∧ (p5 ∧ p2))) ∧ True) ∧ p1)) ∨ False)) ∨ p3)) ∨ p4) ∨ (p4 → True))) := by
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
theorem thm_5_vars_47213780433673764564370443048 : (((((p4 → True) ∧ (False ∧ (p3 ∨ ((p5 ∨ p4) ∧ False)))) ∨ (p4 ∨ ((((False ∨ p1) ∨ (p1 ∧ p1)) ∧ p3) → True))) ∨ (p4 ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184160684182549048304535155755 : (((p4 ∨ ((True ∨ ((p1 → p1) ∧ True)) → (p4 ∨ False))) ∨ True) ∨ ((((p3 ∧ p4) ∧ p5) ∧ (p4 ∧ p3)) ∧ (((True ∨ p4) ∨ p5) ∧ True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249702603498619344165722991104 : ((p5 ∨ p4) ∨ (True → ((((p2 ∨ ((p3 ∧ p1) ∧ p2)) ∧ (p5 ∨ (p3 → p5))) ∧ ((p2 ∨ p5) → p1)) → (((p2 ∧ True) ∧ p1) ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h11.left
    let h14 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h15 =>
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h16 =>
      -- One of the premise coincides with the conclusion.
      exact h12
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h17 := h2.left
  let h18 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h19 := h17.left
  let h20 := h17.right
  -- Disjunctions on the left can always be decomposed.
  cases h19
  case inl h21 =>
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h22 =>
      -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
      have h23 : (p2 ∨ p5) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h21
      -- We have shown the premise of h18, we can now drive its conclusion.
      let h24 := h18 h23
      -- One of the premise coincides with the conclusion.
      exact h24
    case inr h25 =>
      -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
      have h26 : (p2 ∨ p5) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h21
      -- We have shown the premise of h18, we can now drive its conclusion.
      let h27 := h18 h26
      -- One of the premise coincides with the conclusion.
      exact h27
  case inr h28 =>
    -- Conjunctions on the left can always be decomposed.
    let h29 := h28.left
    let h30 := h28.right
    -- Conjunctions on the left can always be decomposed.
    let h31 := h29.left
    let h32 := h29.right
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h33 =>
      -- One of the premise coincides with the conclusion.
      exact h32
    case inr h34 =>
      -- One of the premise coincides with the conclusion.
      exact h32
  -- Conjunctions on the left can always be decomposed.
  let h35 := h2.left
  let h36 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h37 := h35.left
  let h38 := h35.right
  -- Disjunctions on the left can always be decomposed.
  cases h37
  case inl h39 =>
    -- Disjunctions on the left can always be decomposed.
    cases h38
    case inl h40 =>
      -- We want to use the implication h36 based on <expert-advice>. So we show its premise.
      have h41 : (p2 ∨ p5) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h39
      -- We have shown the premise of h36, we can now drive its conclusion.
      let h42 := h36 h41
      -- One of the premise coincides with the conclusion.
      exact h42
    case inr h43 =>
      -- We want to use the implication h36 based on <expert-advice>. So we show its premise.
      have h44 : (p2 ∨ p5) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h39
      -- We have shown the premise of h36, we can now drive its conclusion.
      let h45 := h36 h44
      -- One of the premise coincides with the conclusion.
      exact h45
  case inr h46 =>
    -- Conjunctions on the left can always be decomposed.
    let h47 := h46.left
    let h48 := h46.right
    -- Conjunctions on the left can always be decomposed.
    let h49 := h47.left
    let h50 := h47.right
    -- Disjunctions on the left can always be decomposed.
    cases h38
    case inl h51 =>
      -- One of the premise coincides with the conclusion.
      exact h50
    case inr h52 =>
      -- One of the premise coincides with the conclusion.
      exact h50



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227708810826213089186660999184 : ((p1 ∧ (p2 ∧ p5)) ∨ ((False ∨ (p2 → False)) ∨ (p1 ∨ ((((p2 ∨ True) ∧ ((p5 ∧ p1) ∧ (p5 ∧ (p2 ∧ True)))) → p1) ∧ (True ∨ p3))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h6.left
    let h10 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h3.left
    let h15 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h14.left
    let h17 := h14.right
    -- Conjunctions on the left can always be decomposed.
    let h18 := h15.left
    let h19 := h15.right
    -- Conjunctions on the left can always be decomposed.
    let h20 := h19.left
    let h21 := h19.right
    -- One of the premise coincides with the conclusion.
    exact h17
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177709317774496431768596694015 : ((((((True ∨ True) → p4) ∧ (p1 ∨ p1)) ∧ ((p1 ∨ p1) ∧ p5)) ∧ p1) ∨ ((True ∨ p1) → (p2 → ((p1 ∨ p5) ∨ ((p4 ∧ p5) → p2))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_856467752605489942918468090098 : ((((((p5 ∧ (True ∨ ((p3 ∧ p3) ∧ True))) ∨ ((p3 ∨ p5) ∨ ((((p1 → ((p1 ∧ p4) ∧ p4)) ∨ True) ∧ p2) ∧ False))) ∨ True) → p4) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p5 ∧ (True ∨ ((p3 ∧ p3) ∧ True))) ∨ ((p3 ∨ p5) ∨ ((((p1 → ((p1 ∧ p4) ∧ p4)) ∨ True) ∧ p2) ∧ False))) ∨ True) := by
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
theorem thm_5_vars_785927952337309058158107260622 : (((p4 ∨ ((p5 ∨ (((p4 ∧ ((p5 ∨ p5) ∧ (True ∨ p5))) ∨ (p2 → ((True → ((False ∧ True) → True)) ∨ p4))) ∧ p5)) ∧ (p2 ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654863398655390028967570304303 : ((((((p4 → (p3 ∨ (p1 → ((((False ∨ p1) → (True ∨ True)) ∨ True) → (p1 ∨ p1))))) → (p3 ∨ (p1 → p4))) → p1) ∨ (p5 ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_477528525672216959271827385708 : (((((True ∧ (True ∨ (p1 ∨ (True ∨ (True ∨ p5))))) → p4) → (((False ∨ True) → (p4 → p5)) ∨ ((p3 → p3) ∨ (p3 → (p2 ∨ False))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166514483040681012883212335043 : ((p4 ∨ ((p3 ∨ ((True → ((True ∧ (p5 ∧ p1)) → p1)) → (p4 → False))) ∨ (True ∨ p5))) ∨ (p1 ∨ (p4 ∨ ((p3 → True) → (p3 → p1))))) := by
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
theorem thm_5_vars_66077555801866578509602868418 : ((p5 ∨ ((p5 ∧ ((p2 ∧ (p2 → False)) ∧ (True ∧ (((p5 ∨ p4) → ((True ∧ ((p5 → True) ∨ p5)) ∧ (False ∧ False))) ∨ p4)))) ∨ True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197770247326795195349372021630 : (((p4 ∨ (False → p5)) ∧ (p5 → (p4 ∧ False))) ∨ ((p4 → True) ∨ (p5 ∧ (((((p4 ∧ False) ∧ False) → p4) → False) → (False ∨ (p2 → p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124483272894021435938843996004 : ((((p1 ∨ ((p2 ∨ p2) → False)) ∧ p5) ∧ ((((p5 ∧ (p1 ∧ True)) ∧ p2) ∧ ((False ∨ p2) ∧ ((False → p3) ∨ p1))) ∨ p3)) → (False ∨ True)) := by
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
    cases h3
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h10.left
      let h13 := h10.right
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Conjunctions on the left can always be decomposed.
      let h16 := h9.left
      let h17 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h18 =>
        -- False on the left can always be used.
        apply False.elim h18
      case inr h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h21 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h22 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h23 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h24 =>
      -- Conjunctions on the left can always be decomposed.
      let h25 := h24.left
      let h26 := h24.right
      -- Conjunctions on the left can always be decomposed.
      let h27 := h25.left
      let h28 := h25.right
      -- Conjunctions on the left can always be decomposed.
      let h29 := h27.left
      let h30 := h27.right
      -- Conjunctions on the left can always be decomposed.
      let h31 := h30.left
      let h32 := h30.right
      -- Conjunctions on the left can always be decomposed.
      let h33 := h26.left
      let h34 := h26.right
      -- Disjunctions on the left can always be decomposed.
      cases h33
      case inl h35 =>
        -- False on the left can always be used.
        apply False.elim h35
      case inr h36 =>
        -- Disjunctions on the left can always be decomposed.
        cases h34
        case inl h37 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h38 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h39 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47979341144693025009764252921 : (((((p4 ∧ (p4 ∨ (((((False ∧ False) ∨ p3) → p1) ∧ (True → True)) → p3))) ∧ p4) → (False ∧ (True → (p3 ∧ p5)))) → (p4 ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



