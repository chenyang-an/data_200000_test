variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1611447364183535173892787106 : (((True ∧ ((((p5 ∨ (p2 ∨ p2)) ∧ (True → (p3 ∨ (p4 → False)))) ∧ (True → (p1 ∨ p2))) ∨ p3)) ∨ (p5 → p3)) → (p4 ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
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
    case inr h14 =>
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
theorem thm_5_vars_136191677036788736066004322944 : ((((p3 ∨ p4) ∧ (p3 ∧ (False ∧ False))) ∧ ((((p3 ∨ p3) ∧ ((False → (p3 ∨ True)) ∧ True)) ∨ p1) ∨ (True ∨ p4))) ∨ ((True ∨ p3) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52077134583471478860781544478 : (((((p1 ∧ p5) → ((False ∧ ((p2 ∧ p2) ∧ ((p1 ∧ p5) ∧ p4))) ∨ p5)) ∧ True) → (((p4 ∧ p5) ∧ p2) ∨ ((True ∧ p1) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184096094918778075531206013439 : (((((p4 → p1) → p2) → (p2 ∧ ((p4 → p3) → p4))) ∨ p4) ∨ (True ∨ ((((True ∧ p3) ∧ p4) ∨ p1) ∨ (p1 → (p5 → (p5 → False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624269463696796182358626020936 : ((((p3 ∨ (((((p2 ∨ ((p1 → False) ∨ (p2 ∨ p5))) ∧ (p3 ∧ (True → True))) ∨ (False → p2)) ∧ (True ∧ p5)) ∧ (p3 → p3))) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_350266301094389345620766163723 : (p4 → ((p3 ∧ ((((p5 ∧ p2) ∨ (p1 ∨ True)) → (p2 ∨ (((((p1 ∨ p3) ∨ True) ∨ p4) ∨ p4) ∧ p4))) ∨ (True → (p1 ∨ p1)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310128373340055560121333418377 : (p2 ∨ (((p1 ∨ False) ∧ (((True ∧ False) → ((p2 ∨ (False ∧ p1)) → p4)) → p2)) ∨ ((p4 ∧ False) → (True → ((p2 → (p5 → p5)) ∧ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620615244277284988529473734345 : (((((p5 → p4) ∨ (p5 ∨ (p4 → (((True ∨ ((((p4 ∧ p3) ∧ p5) ∨ (p4 → p3)) ∨ (p5 → p5))) → p1) ∨ (True ∨ True))))) ∨ False) ∨ p2) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319274058610170010721658107915 : (p4 ∨ ((((((True ∧ (p4 ∧ p5)) ∧ p3) → (p5 ∨ p1)) → p5) ∨ ((False → p2) ∨ p4)) ∨ ((p1 → (p5 ∨ p3)) ∨ ((p2 ∧ p3) ∨ True)))) := by
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
theorem thm_5_vars_45752450972090187694322655989 : (((False → (((p5 → (((False ∧ p5) → (((False → p4) ∧ p5) ∧ (p3 ∧ p2))) → (False ∨ p4))) ∨ True) → (p2 → (p2 ∨ False)))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183881885462136136004556732150 : ((((False ∨ (p5 ∧ p5)) ∨ ((p1 → (False ∧ p1)) → p1)) ∧ False) ∨ ((p5 → (p2 ∨ ((p5 ∨ ((p5 ∧ (p2 ∨ p5)) ∧ p1)) ∨ p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229130274879590107967363612080 : ((True → (p3 ∧ p4)) ∨ (((p4 → ((p2 ∧ p4) → p5)) ∧ (p2 ∧ ((True ∧ p2) ∨ (p4 → (((p5 ∨ p5) ∧ False) ∧ (p4 → p4)))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344188816296599332623569940174 : (p2 → (p1 ∨ ((False ∧ ((p1 ∨ ((p1 ∨ False) → (p1 ∧ False))) ∨ p1)) ∨ (((((p1 → p3) ∧ ((False ∧ True) ∧ False)) → False) ∨ p3) ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121989286376248279578123539514 : (((p2 ∨ ((True ∧ p1) → (((p3 → ((False ∧ p4) ∨ p5)) ∧ p3) ∨ (((False ∨ p1) ∨ p2) ∨ ((False ∨ True) ∨ p1))))) → False) → (True ∧ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 ∨ ((True ∧ p1) → (((p3 → ((False ∧ p4) ∨ p5)) ∧ p3) ∨ (((False ∨ p1) ∨ p2) ∨ ((False ∨ True) ∨ p1))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62358983352750517469039416028 : ((p3 ∧ ((p3 → ((p1 ∧ (p5 ∧ ((p4 ∨ (p1 → p3)) ∨ ((p4 → (p4 ∨ p5)) → p4)))) ∨ False)) ∨ (True ∧ ((False ∧ True) → p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49693152336617468325437981495 : ((((p4 ∨ False) ∨ (((True → (((p4 → p5) → ((p1 ∧ p4) ∧ p1)) → (p4 ∨ (False → p4)))) ∨ p4) → p4)) → (p4 ∨ (True → p3))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h4 =>
      -- False on the left can always be used.
      apply False.elim h4
  case inr h5 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : ((True → (((p4 → p5) → ((p1 ∧ p4) ∧ p1)) → (p4 ∨ (False → p4)))) ∨ p4) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- False on the left can always be used.
      apply False.elim h9
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h10 := h5 h6
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_730157859877146817151155277248 : (((((p5 ∨ p4) → True) → (p5 → (((((p2 → p4) ∨ p5) ∧ p3) ∧ (True → ((p1 → p4) ∨ ((p2 ∧ (False ∨ p5)) → p1)))) ∨ p5))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148806108932867030766905113536 : (((((p2 → p4) ∨ (p4 ∧ True)) → False) → ((True → ((p2 → True) ∨ p4)) → ((p2 ∨ True) ∧ (p2 ∧ p4)))) ∨ (False → (p5 ∧ (p1 ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_156726464370448828771727980476 : ((((((True ∨ p2) ∨ p4) ∧ (False ∧ True)) ∨ (p1 ∨ (((p5 ∨ (p5 → False)) → p5) ∧ p2))) ∧ p2) ∨ (((p2 ∨ False) → p5) → (True → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353835480202639120026068855429 : (p4 → (p1 → (((p3 ∧ (((((p1 ∧ p2) → ((p2 → (True ∧ p1)) ∧ (True ∧ (False → p4)))) ∨ p5) → p1) → (p2 ∧ p2))) ∨ True) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135108045789496898242906745182 : (((((p3 ∨ p4) ∧ p1) ∨ (False ∨ ((((p4 ∧ ((p3 ∨ False) ∧ (p3 ∧ p2))) ∧ p5) → p3) → False))) ∨ (False → True)) ∨ (p2 → (p3 ∧ p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_120131602067234862164403467250 : (((((p1 → True) ∨ p3) ∨ (((p3 ∨ ((True ∧ p3) ∨ p4)) ∧ p4) ∨ (False → ((((p3 ∧ False) → True) → p1) ∧ p2)))) ∧ True) → (False ∨ True)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- Conjunctions on the left can always be decomposed.
          let h14 := h13.left
          let h15 := h13.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h16 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300193804791294806217491152752 : (False ∨ ((((((((p1 → False) ∧ p1) → True) ∧ p4) ∨ (((p3 → p1) ∧ (p5 → True)) ∧ p4)) ∨ (p5 ∨ (p2 → True))) → p3) → (p3 ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((((p1 → False) ∧ p1) → True) ∧ p4) ∨ (((p3 → p1) ∧ (p5 → True)) ∧ p4)) ∨ (p5 ∨ (p2 → True))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_17293344065668421032115778945 : (((((True ∨ p3) → p2) ∧ (False → ((True ∧ p4) → (p2 ∨ (p5 → (((p5 → True) ∧ (p3 ∧ p2)) ∧ False)))))) → ((p5 ∨ False) ∨ p2)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (True ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313276423308511394307650977182 : (p3 ∨ ((p2 ∧ (((((((p4 ∧ p2) → p2) ∨ ((p1 → True) ∧ p2)) ∨ p4) ∧ (True → False)) ∧ False) ∧ (p3 ∨ (p5 ∧ (p4 ∧ True))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314007408576478743071067749479 : (p3 ∨ ((p1 ∧ ((p2 → (((p3 ∧ p3) → (p1 → (True ∧ p3))) → (p4 → (p5 ∧ False)))) ∨ (p2 → ((p4 ∨ p4) ∧ p3)))) ∨ (False → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134104186295227194812195136924 : (((((((((p3 ∨ (False ∨ (p4 ∧ p5))) ∧ p2) ∨ True) → p1) → ((p4 ∧ False) ∧ p2)) ∧ p3) ∧ (p3 ∧ p1)) ∨ p3) ∨ ((False ∨ True) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190071929002410710934608966015 : (((((p5 ∨ False) → (p1 ∧ (False → p5))) → False) ∧ p3) ∨ ((((((p1 ∨ p2) → p3) ∧ p2) ∧ ((p4 ∨ True) → False)) ∧ p3) ∨ (True ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62883910787743598287737857372 : ((p4 ∧ ((False ∨ p2) ∧ (((p1 ∧ ((False ∨ ((False → (((((p5 ∨ False) ∨ p5) ∨ p1) → p4) → p5)) ∧ p2)) → p1)) ∨ p4) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187808649669706573013752058330 : ((p4 → (((p1 → False) → (((p5 ∧ p5) → p4) ∧ p1)) ∨ p3)) → ((p5 → ((p4 ∨ False) ∨ (p5 → p3))) ∨ ((True ∧ False) → (False ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60029337806341083956571152413 : (((p1 ∨ p2) → (p2 ∨ ((((((False → p1) → (((p3 ∧ p4) ∨ (p3 ∧ False)) ∨ p2)) ∨ p4) ∧ (p1 ∨ False)) ∧ p1) ∨ (False ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310773758438894192455146716390 : (p2 ∨ (((p4 → p5) ∧ p1) ∨ ((p3 ∧ (((p2 ∨ ((p4 → p2) ∨ p3)) → (p5 → (p5 ∧ (p2 ∧ ((p4 ∧ p2) ∨ p1))))) ∧ p5)) → p2))) := by
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
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : (p2 ∨ ((p4 → p2) ∨ p3)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h9 := h7 h8
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- One of the premise coincides with the conclusion.
  exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149137013894830750071992679714 : (((p4 ∧ p4) ∧ (p1 ∧ ((p4 → True) ∧ (((False ∨ ((p3 ∧ p2) ∧ (p4 ∨ p4))) ∨ (p4 ∨ p1)) ∧ False)))) ∨ (False → (True ∨ (p2 ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622990391496822911031788855075 : ((((p5 ∧ ((p2 ∧ p4) ∧ ((p1 ∨ (True ∧ (p3 ∧ ((p2 → (p1 → (True → (p3 ∨ p3)))) → p2)))) ∧ (p4 ∧ (p5 ∨ True))))) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_253001708985261887046184736652 : ((True ∧ p3) → ((((p5 ∧ (True ∨ p2)) ∨ p1) ∧ (((False ∨ True) ∨ True) → ((p2 → p3) ∧ (True ∧ ((False ∨ p3) ∧ (False ∧ p1)))))) → p4)) := by
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
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h1.left
      let h10 := h1.right
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h11 : ((False ∨ True) ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h12 := h4 h11
      -- We need to get the right conjuct of h12 based on <expert-advice>.
      let h13 := h12.right
      -- We need to get the right conjuct of h13 based on <expert-advice>.
      let h14 := h13.right
      -- We need to get the right conjuct of h14 based on <expert-advice>.
      let h15 := h14.right
      -- We need to get the left conjuct of h15 based on <expert-advice>.
      let h16 := h15.left
      -- False on the left can always be used.
      apply False.elim h16
    case inr h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h1.left
      let h19 := h1.right
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h20 : ((False ∨ True) ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h21 := h4 h20
      -- We need to get the right conjuct of h21 based on <expert-advice>.
      let h22 := h21.right
      -- We need to get the right conjuct of h22 based on <expert-advice>.
      let h23 := h22.right
      -- We need to get the right conjuct of h23 based on <expert-advice>.
      let h24 := h23.right
      -- We need to get the left conjuct of h24 based on <expert-advice>.
      let h25 := h24.left
      -- False on the left can always be used.
      apply False.elim h25
  case inr h26 =>
    -- Conjunctions on the left can always be decomposed.
    let h27 := h1.left
    let h28 := h1.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h29 : ((False ∨ True) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h30 := h4 h29
    -- We need to get the right conjuct of h30 based on <expert-advice>.
    let h31 := h30.right
    -- We need to get the right conjuct of h31 based on <expert-advice>.
    let h32 := h31.right
    -- We need to get the right conjuct of h32 based on <expert-advice>.
    let h33 := h32.right
    -- We need to get the left conjuct of h33 based on <expert-advice>.
    let h34 := h33.left
    -- False on the left can always be used.
    apply False.elim h34



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307712380806159808507686501468 : (p1 ∨ (p2 → (p3 ∨ ((p2 → (p2 → False)) ∨ (p4 → ((False ∨ ((((True ∨ (False ∨ p2)) ∨ (True ∨ p5)) → (False ∨ True)) ∨ p3)) ∨ p1)))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248586355027768899212585235485 : ((p3 ∨ False) ∨ (((p1 → (p2 ∧ p1)) ∨ ((p5 ∨ False) ∨ p3)) ∨ ((True ∨ False) ∨ ((p4 ∧ ((p4 ∨ True) ∨ (p3 ∧ (False → p5)))) ∨ False)))) := by
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
theorem thm_5_vars_169066646138543920649010527973 : ((p3 → ((p1 ∧ ((p2 ∧ (p1 ∨ (True ∨ (p1 ∧ p2)))) ∨ True)) → (p5 ∧ (False ∧ p5)))) → (True → (p5 ∨ (p1 ∨ (p2 → (True → True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250929205791709814597372658829 : ((p1 → p4) ∨ (((((False → ((p2 → ((p1 ∨ ((False → (False → p4)) ∨ (p2 → (p3 → p3)))) ∨ True)) ∧ p4)) ∨ False) ∨ p4) → p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137163110458944637899944862366 : ((False ∧ ((((p5 ∧ p2) ∨ p3) ∧ ((p2 ∨ ((p4 → p3) ∧ (((p1 → p3) ∨ (p2 ∧ p1)) ∨ p3))) ∧ p3)) → p5)) ∨ (False → (p5 ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_752794644517623167357935018289 : (((False ∧ ((p4 ∧ (p3 ∨ (((p5 ∨ ((p5 ∨ ((p1 → (True → p5)) ∧ False)) → p3)) ∧ p2) ∧ (False ∧ ((p3 → True) → p3))))) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114359762605421270704822782082 : ((((((False ∨ p1) → (((p5 → (p2 → p2)) → True) ∧ False)) → ((p5 ∨ p2) ∧ True)) ∧ p5) ∨ (p1 → (True ∨ (p5 → True)))) ∨ (p4 ∨ p5)) := by
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
theorem thm_5_vars_707744131833562432311769770564 : (((((False → p1) → ((p5 ∨ p2) ∨ (False ∧ False))) ∨ (((p4 ∨ (((False → (False ∧ p3)) ∨ ((p1 ∧ p4) ∧ p1)) ∨ p1)) → p5) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659992211292921058697370459717 : ((((((((((False → ((True ∧ False) ∨ p2)) ∧ p5) ∨ False) ∧ (((p3 ∨ (p1 ∧ False)) ∧ p5) → p1)) ∧ p2) → True) ∨ p2) → (False ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_719815791416564841121062428545 : ((((p2 → (p5 ∨ (p2 ∧ p5))) ∨ ((True → p2) → (((True → ((True → (False ∨ p2)) ∨ p2)) ∨ (p1 ∧ (p3 ∨ False))) ∧ (True → False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122769656723034203563007772093 : (((p4 ∨ (((p4 ∧ (p2 → (p5 → (p1 → (p4 ∧ p1))))) ∨ ((p3 ∧ ((p4 ∨ p5) ∨ p1)) → p4)) ∨ True)) → (False ∧ True)) → (True ∧ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p4 ∨ (((p4 ∧ (p2 → (p5 → (p1 → (p4 ∧ p1))))) ∨ ((p3 ∧ ((p4 ∨ p5) ∨ p1)) → p4)) ∨ True)) := by
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60801978530643595334254671856 : ((True ∧ (p1 ∧ ((p1 → p3) ∧ (((p2 ∧ (p5 ∨ ((False → p3) ∧ p1))) ∧ p4) ∧ ((False → (False → ((p3 → p5) ∨ p2))) → p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119399764473634535811117062474 : ((p4 → (((False ∧ ((p3 ∨ False) → ((p2 ∨ (((p2 ∨ p1) ∨ ((True ∧ p5) ∧ (p4 → p4))) ∧ p5)) ∨ p4))) ∨ p3) ∨ True)) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47012902253115394470773369804 : ((((p2 ∧ (((p3 ∨ (p2 ∧ ((p4 → (((p5 ∨ (p1 → True)) ∧ False) → p5)) ∨ True))) ∨ False) → (False → False))) → p4) ∨ (p4 ∨ True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690640871739222554429177531381 : (((((((p2 → p2) ∨ True) ∧ ((p4 ∧ ((p5 ∨ p4) ∧ p4)) → (p1 ∨ p5))) ∨ p3) → (((((True → p4) ∧ p5) ∨ p5) ∨ p1) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116091883575172071754682814856 : ((((p5 ∨ True) ∨ p2) ∧ ((((((p4 ∨ p1) ∧ p4) → ((p2 ∨ (p1 ∨ p3)) ∧ (p4 → p2))) → (True ∧ p4)) ∨ p5) ∨ p2)) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_759674425682078869207741845160 : (((p2 ∧ ((p2 → ((p3 ∨ ((False ∧ p1) ∧ False)) ∨ (p5 ∧ ((p4 ∨ p1) ∨ p3)))) → ((p4 ∧ False) ∨ (((p1 → p3) ∧ False) ∧ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55728908794907199906235284075 : (((((p3 ∨ p4) ∨ True) → p2) ∧ ((((False ∧ True) ∨ ((p1 ∧ True) ∧ (p5 → False))) ∨ p2) ∨ (False ∧ (p5 ∧ ((False ∨ True) ∧ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669844471842700638168544187335 : (((((p2 → ((p4 ∧ p3) ∨ (p3 ∨ (True ∨ ((p5 → True) → p2))))) ∧ (p5 ∨ (p2 → (p1 → (p3 ∨ p2))))) ∨ (p5 ∧ (p2 → True))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181218831387788441925498786932 : ((p2 ∧ (p3 ∨ (p3 ∧ (p5 → (((p1 ∨ p5) ∧ (True ∧ p2)) ∨ p5))))) → (p3 ∧ (p4 → ((True ∧ p1) → (((p3 ∨ p2) → False) → False))))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h6
  -- Implications on the right can always be decomposed.
  intro h8
  -- Implications on the right can always be decomposed.
  intro h9
  -- Implications on the right can always be decomposed.
  intro h10
  -- Conjunctions on the left can always be decomposed.
  let h11 := h9.left
  let h12 := h9.right
  -- Conjunctions on the left can always be decomposed.
  let h13 := h1.left
  let h14 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h14
  case inl h15 =>
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h16 : (p3 ∨ p2) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h15
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h17 := h10 h16
    -- False on the left can always be used.
    apply False.elim h17
  case inr h18 =>
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h21 : (p3 ∨ p2) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h19
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h22 := h10 h21
    -- False on the left can always be used.
    apply False.elim h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171856940226327073627562647802 : ((((p5 ∨ True) → (p4 → (True ∧ ((p5 ∧ ((p5 ∨ True) ∨ p1)) ∧ True)))) → p4) ∨ (((((p2 ∨ (p2 ∧ False)) ∧ p4) ∧ p1) → p4) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50277846148129491962083153343 : ((((p1 ∧ (((((False ∨ p4) ∨ False) ∧ p1) → p1) ∨ (((p5 ∧ p5) → p3) → p3))) ∨ (False ∨ p1)) ∨ (p4 → ((True ∧ p5) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265548702391717891157136313885 : (True ∧ (False ∨ ((p1 → p1) → (((p4 ∨ ((p1 ∧ (p5 → p2)) → False)) ∧ p2) ∨ (p3 → (((p2 ∧ ((p4 ∨ False) ∨ p4)) ∧ p1) ∨ p3)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_358714828972518482545283913869 : (p5 → (p5 → ((p2 → (((False ∨ (p3 → ((True → p3) ∨ ((p3 ∧ (((p1 ∧ True) ∨ True) ∨ p4)) ∨ p4)))) ∨ False) → False)) ∨ (p3 → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206401664243624517544989643316 : ((p3 ∨ ((p1 ∨ p4) ∧ (True ∧ p4))) ∨ (False ∨ (((True → (((True → p2) → ((False ∨ False) ∧ p2)) → p3)) ∧ False) ∨ (p1 → (p2 → p1))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64786164435219070907022841490 : ((p2 ∨ ((((p2 ∨ p4) → ((((p3 ∨ (p4 → p1)) ∧ ((p4 ∧ p3) ∨ p3)) → (p3 ∨ p3)) ∨ p2)) → ((p5 → p5) ∧ p2)) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164738756302250942711292842400 : (((((p2 → p5) ∧ ((((False → p5) → p1) → (p3 ∧ False)) ∧ p4)) ∧ (p5 ∨ p5)) ∨ False) ∨ ((p1 → (True ∨ (False ∧ True))) → (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619541087780776767034716320544 : (((((True ∧ True) ∧ ((((p2 → (p5 ∧ True)) → (False ∨ p1)) → p3) → ((p5 ∨ ((p1 ∨ (True ∨ p1)) → p4)) → (True → p5)))) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_721114599666171719726150112477 : (((((p4 ∨ p3) ∨ (p2 ∧ p1)) → ((p5 ∧ (((p5 ∨ p5) ∨ p4) → p1)) ∧ ((p3 ∨ (True ∨ p1)) ∧ ((p1 → (p4 ∧ p5)) → True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_724988131539173673378143924897 : ((((True → (p3 ∨ p5)) ∧ (((p1 ∧ p4) ∨ p2) ∧ ((((p5 → False) ∨ ((p2 → p5) ∨ p1)) ∧ (p3 → p3)) ∧ (False ∨ (p4 ∨ p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341063780185390156042025316428 : (p2 → ((p4 ∨ ((((((p3 ∧ p4) ∨ ((False ∧ p5) ∧ False)) ∧ ((p3 ∧ p3) ∧ p4)) ∨ p5) ∧ ((False → (p3 → p5)) → p3)) ∨ True)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159621986070340051439442805649 : ((((p2 ∨ (p3 → ((False ∨ p2) ∨ ((((p2 ∨ p4) ∨ p3) ∨ (False ∨ p1)) → True)))) ∧ p4) ∨ p3) → ((((True ∧ p3) ∨ p5) ∨ p2) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
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
theorem thm_5_vars_357269392990575958324758474845 : (p5 → ((p3 ∧ p2) ∨ ((False ∨ ((p2 → p3) → ((p3 ∨ p1) ∧ (((p5 ∨ p1) ∧ True) ∧ p3)))) ∨ ((p1 ∨ (True → p5)) ∨ (p1 ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312230068829403416203266731861 : (p2 ∨ (p1 → ((((p2 ∧ (False ∧ True)) ∨ ((p2 ∨ False) ∨ True)) ∨ ((p1 ∨ (p2 → ((p2 ∨ (p5 → p1)) ∧ True))) → (True → p4))) ∨ p2))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138594505769419468271280551127 : ((((p3 ∨ (((((((p4 → True) ∨ (False ∧ p4)) ∧ (p3 → True)) → p4) ∧ (p2 → True)) ∨ True) ∨ True)) → p3) ∧ p2) → ((p2 ∨ p2) → p3)) := by
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
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h6 : (p3 ∨ (((((((p4 → True) ∨ (False ∧ p4)) ∧ (p3 → True)) → p4) ∧ (p2 → True)) ∨ True) ∨ True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h7 := h4 h6
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h1.left
    let h10 := h1.right
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h11 : (p3 ∨ (((((((p4 → True) ∨ (False ∧ p4)) ∧ (p3 → True)) → p4) ∧ (p2 → True)) ∨ True) ∨ True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h12 := h9 h11
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336106788126127146604648124303 : (p1 → (((((p4 → (((p3 ∨ True) ∧ p5) ∨ (p2 → p3))) → ((True ∧ p3) ∧ ((((p3 → p4) → p5) → p1) ∨ p5))) ∧ p5) ∨ p1) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_725843806143313004205281874308 : (((((p5 ∨ p5) ∧ p4) ∨ (p5 → (((p1 → p1) ∨ p4) ∧ ((((((True → p5) ∨ False) → p1) → (True ∧ p1)) ∧ (p5 → p5)) → p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148115751447105082043484021577 : (((((((p4 ∧ p1) ∨ p1) ∨ p4) ∨ p2) ∧ ((((p1 ∧ (p5 → False)) ∨ p1) ∧ p4) ∧ p4)) → (p3 ∨ p4)) ∨ ((p5 ∨ p5) → (p5 ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350028801499330511621892777872 : (p4 → (((((((p3 → (p5 → ((p1 → True) → (p1 ∨ ((p1 ∨ False) ∧ p2))))) ∨ p4) ∨ p3) → p2) → ((True ∨ p2) ∨ p4)) → False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309707241864695679571594599061 : (p2 ∨ (((True → False) ∧ (((True → p2) → (False ∧ (False ∨ p1))) → (((p5 → (False ∧ (True ∨ True))) ∨ p2) ∧ True))) → (p5 ∧ (True ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186671693302496526122086912311 : ((((p3 ∨ True) ∨ ((True → p3) ∧ p2)) ∧ ((p5 ∨ False) → p4)) → (((p4 ∧ ((False ∨ p2) ∧ ((False → p5) ∨ False))) ∨ (False ∧ p4)) → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h1.left
        let h12 := h1.right
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h13 =>
          -- Disjunctions on the left can always be decomposed.
          cases h13
          case inl h14 =>
            -- One of the premise coincides with the conclusion.
            exact h4
          case inr h15 =>
            -- One of the premise coincides with the conclusion.
            exact h4
        case inr h16 =>
          -- Conjunctions on the left can always be decomposed.
          let h17 := h16.left
          let h18 := h16.right
          -- One of the premise coincides with the conclusion.
          exact h4
      case inr h19 =>
        -- False on the left can always be used.
        apply False.elim h19
  case inr h20 =>
    -- Conjunctions on the left can always be decomposed.
    let h21 := h20.left
    let h22 := h20.right
    -- False on the left can always be used.
    apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_728015239415272803753428925066 : ((((p3 ∨ (p1 → p5)) ∨ ((p1 ∧ ((((p4 ∧ p3) → p4) ∨ (p5 → p3)) ∧ ((True ∨ p4) ∨ p3))) → ((True ∨ (p4 ∨ True)) ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55265588974091694705243715811 : ((((p3 ∧ p3) → ((p5 → p4) → p4)) ∨ ((((False ∨ False) ∧ p4) ∨ (((p4 → (p1 → p3)) ∨ p1) ∧ p2)) → ((p1 → False) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_89009599110086782278999660590 : ((((p2 ∨ True) ∧ True) ∧ ((False ∨ (((p1 ∧ p5) ∨ (True ∨ p2)) → (False ∧ (True ∧ ((p2 → (p1 ∧ p5)) → p5))))) ∧ (p1 ∨ True))) → False) := by
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
    let h7 := h3.left
    let h8 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h11 =>
        -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
        have h12 : ((p1 ∧ p5) ∨ (True ∨ p2)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h10, we can now drive its conclusion.
        let h13 := h10 h12
        -- We need to get the left conjuct of h13 based on <expert-advice>.
        let h14 := h13.left
        -- False on the left can always be used.
        apply False.elim h14
      case inr h15 =>
        -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
        have h16 : ((p1 ∧ p5) ∨ (True ∨ p2)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h10, we can now drive its conclusion.
        let h17 := h10 h16
        -- We need to get the left conjuct of h17 based on <expert-advice>.
        let h18 := h17.left
        -- False on the left can always be used.
        apply False.elim h18
  case inr h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h3.left
    let h21 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h22 =>
      -- False on the left can always be used.
      apply False.elim h22
    case inr h23 =>
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h24 =>
        -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
        have h25 : ((p1 ∧ p5) ∨ (True ∨ p2)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h23, we can now drive its conclusion.
        let h26 := h23 h25
        -- We need to get the left conjuct of h26 based on <expert-advice>.
        let h27 := h26.left
        -- False on the left can always be used.
        apply False.elim h27
      case inr h28 =>
        -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
        have h29 : ((p1 ∧ p5) ∨ (True ∨ p2)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h23, we can now drive its conclusion.
        let h30 := h23 h29
        -- We need to get the left conjuct of h30 based on <expert-advice>.
        let h31 := h30.left
        -- False on the left can always be used.
        apply False.elim h31



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_128458194316755205663654801523 : ((p5 → ((((p5 → ((True ∧ False) → (p5 → p1))) ∨ (False ∨ ((((True ∨ p3) ∧ p4) → p3) → p2))) → (p3 ∨ False)) → p5)) → (p2 ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780302332235884835559722141154 : (((p2 ∨ ((((((p5 ∧ p4) ∧ (p3 → p3)) ∧ (p2 ∧ p4)) ∨ ((p3 ∨ (p5 ∧ p2)) ∧ p3)) ∧ p2) ∨ (False → ((p5 → p5) → False)))) ∨ p4) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157212507050484736173276781555 : ((((p3 → ((p1 ∧ p3) → (((p3 → False) ∨ (p1 → p4)) → (False ∧ True)))) → (p1 → p2)) → False) ∨ ((((p2 ∧ p4) ∧ False) → p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175141679012496841061479779640 : ((p5 ∧ ((p1 ∨ ((False → p5) → (p2 ∧ p1))) → (((True ∨ True) ∧ p1) → True))) → (p4 → (((p2 ∨ ((p2 ∧ p2) → True)) ∨ p5) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705096692765773896081739903693 : ((((p5 → (((p1 ∧ p5) ∧ (True → p1)) ∨ (p5 ∧ False))) → (((p2 ∧ p2) ∨ (((p5 ∨ p1) ∧ (True ∧ p1)) → p2)) ∨ (p2 ∨ True))) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_60079066312794150686841441571 : (((p2 ∨ p4) → ((p4 ∧ p5) → ((p1 ∨ ((p3 → (False ∧ ((p4 ∧ (True → p1)) → True))) → (p3 ∧ p5))) ∨ (p3 → (p5 ∨ p3))))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2182641137899170630667302001 : ((((p3 → False) ∧ ((p3 ∨ (p4 ∨ (((p3 ∨ p4) ∨ True) ∨ p2))) ∧ p1)) → p4) ∨ (True ∨ (p2 ∨ (p3 → (False ∨ (True ∧ p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41358125142368021676093724952 : (((((((p1 → (p4 ∧ p1)) → (p5 ∨ p3)) ∨ ((p2 ∧ (p1 → p5)) ∧ p3)) ∨ True) → (p4 ∨ (((True ∨ False) → False) ∨ True))) ∨ False) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h7 := h5.left
      let h8 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326341133303633436256674414197 : (p5 ∨ (p5 → (((((False → (True ∧ p4)) → (False ∨ p5)) ∨ (p1 ∨ (((p2 ∧ p5) ∧ (True → p1)) ∧ (p5 ∨ p3)))) → (p3 ∨ p4)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264963704712429629895096418025 : (True ∧ ((p3 ∨ True) → (True ∧ ((p4 ∧ (((((p2 ∧ p2) → p5) ∧ (False ∨ p2)) ∨ p2) ∨ False)) ∨ (((p1 ∧ p2) → (p3 → p1)) ∨ p1))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_637062061949849288480218668681 : (((((p3 → (p5 ∨ (p5 ∨ (((p4 ∧ p2) ∧ (False ∧ True)) ∨ p2)))) ∧ ((((((p2 ∨ True) ∨ p1) ∨ False) ∧ False) ∨ p4) → p2)) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147080484726769617790821332339 : (((((p1 ∨ (True ∨ p3)) ∨ p1) ∧ (((True ∨ p4) ∧ ((((False ∨ p3) ∧ p2) ∧ p2) ∨ p2)) ∧ p3)) ∧ False) ∨ ((False ∨ False) → (p1 ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45896760579876618900026928536 : (((p4 → ((((p1 → p5) ∨ p1) → ((((p3 → ((False ∧ True) ∨ p5)) → (p3 ∨ True)) ∧ (False → (p5 ∨ p5))) → p2)) ∧ p5)) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68892914020099228975991875170 : ((p4 → (p4 ∧ (((True → (((True ∨ p1) ∧ (((p5 ∨ True) ∨ False) → True)) ∨ ((p1 ∨ True) → False))) → ((p1 → p5) → False)) ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619058009468700761068159152599 : ((((((p3 ∨ p1) → p3) ∨ ((False → p5) ∧ ((((p3 ∧ p5) ∧ (p2 → (p4 ∧ (p3 ∧ p2)))) → (p2 ∨ (p2 → p1))) ∧ p2))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65748914675077459055594251384 : ((p4 ∨ (((p2 ∨ p5) ∧ (p3 ∧ (False → (p5 → ((p2 ∨ p5) ∧ (((True ∨ True) → p5) → (True ∨ p3))))))) → ((p3 ∧ False) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114751009643120744201743268514 : (((p2 ∧ ((((((False ∧ p1) ∨ (p4 ∧ p4)) ∧ (p1 → p4)) ∧ p4) → p2) ∨ p3)) → (True → (p1 ∧ (False ∧ (p3 → False))))) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116975860453254168288836036291 : (((p4 ∧ p4) → ((p4 ∧ p5) ∧ ((((((p2 ∨ True) ∧ p1) ∧ ((p4 ∧ p1) ∨ p2)) ∧ ((False → p3) ∧ p5)) → False) ∧ False))) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246508957934734444020471661599 : ((p5 ∧ p1) ∨ ((False ∨ (((((True ∧ True) ∨ p2) → (p5 ∧ False)) ∧ (True ∨ ((True → p1) ∨ (False ∨ True)))) → (False ∧ p2))) ∨ (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_212696938848078462563512004733 : ((False → ((True ∨ p3) → p3)) ∧ (p2 ∨ ((((p2 ∨ (True ∧ p2)) ∧ (p3 → False)) → ((True ∧ p5) ∨ ((True → p4) → (p5 ∧ p1)))) ∨ True))) := by
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
    apply False.elim h1
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134255870180995674797925213095 : (((((p4 ∧ p4) → p2) ∨ (p4 ∧ ((p4 ∨ (p4 → p4)) ∧ (p3 ∧ (False ∨ (((True ∨ False) → p4) ∧ True)))))) ∨ p4) ∨ (True ∨ (p2 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



