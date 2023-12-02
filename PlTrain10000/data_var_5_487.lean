variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65070395890116701475473851293 : ((p2 ∨ (p4 ∧ (False ∧ (p5 ∨ (p3 ∧ ((p2 ∧ ((p4 ∧ (p1 ∨ p3)) → ((p4 ∧ True) ∧ (((True ∧ p5) ∧ p5) → False)))) ∧ p3)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_800277731329788947046315588420 : (((p2 → (((p5 ∨ (p1 ∧ (((True ∧ (((p1 ∧ (False ∨ (p4 → (p5 ∧ p5)))) → False) ∨ p5)) ∨ False) ∨ False))) ∨ (p2 ∨ p5)) ∨ p5)) ∨ p3) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328709950581106551682999634325 : (True → (((p1 ∨ False) ∨ (p4 ∧ ((p3 → (p1 ∧ False)) → (p5 ∧ p1)))) ∨ (((((p1 → p3) ∨ (p3 ∧ p2)) → (p3 ∨ p2)) ∧ p2) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_19515111359886568068168391033 : ((((p3 ∨ ((((p3 ∧ False) ∧ p4) ∨ False) ∧ ((p5 ∧ p5) ∧ (p2 ∨ p1)))) ∨ p5) ∨ ((((p2 ∧ (p1 → p5)) ∨ p5) ∧ p3) → p3)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    let h5 := h4.left
    let h6 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341998176816105307429012483772 : (p2 → ((((p2 ∧ p2) ∧ p2) ∧ (((p2 ∧ (p5 ∧ (p4 → (((p1 → p1) ∨ (p3 ∧ p2)) → p5)))) ∧ False) ∨ p5)) ∨ (p2 ∧ (True ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609677670069615644784087884433 : (((((p1 ∨ ((((p5 ∨ p3) → (p5 → p2)) ∨ p5) ∧ (((True ∧ (False ∨ (p5 → (p3 ∨ p2)))) ∧ p2) ∨ (p2 ∧ p4)))) ∨ False) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_216045115747711443786663927761 : ((p5 ∨ (False ∧ (False ∧ p5))) ∨ (p5 ∨ ((True ∧ p1) → (p1 ∧ (False ∨ (p5 → (((p5 → p5) → (p4 ∧ p5)) ∨ ((True ∨ p3) ∧ p1)))))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171374319684606543117149382632 : ((((p2 → ((False ∧ ((p1 ∧ p1) ∧ (p2 ∨ p2))) → True)) → (True → p3)) ∧ p5) ∨ (False → ((p5 ∧ (p2 ∨ ((False ∧ p5) ∨ p2))) → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h1
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- False on the left can always be used.
      apply False.elim h8
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_807386312156282246621491321 : ((p1 ∧ ((((True ∨ p2) → (((p2 → p5) → p2) ∧ (False ∨ (p4 ∧ p1)))) ∨ False) ∧ ((p1 ∧ (False ∨ False)) ∧ (p4 → p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150319082081733211554108245973 : ((p4 → (p2 ∨ (((((p4 ∨ p3) ∨ p2) → ((True ∧ (p5 ∨ True)) ∧ (False ∧ p4))) ∧ p2) → (p5 ∧ False)))) ∨ (True ∧ (p2 ∨ (p3 → p4)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : ((p4 ∨ p3) ∨ p2) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- False on the left can always be used.
  apply False.elim h8
  -- Conjunctions on the left can always be decomposed.
  let h9 := h2.left
  let h10 := h2.right
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h11 : ((p4 ∨ p3) ∨ p2) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h12 := h9 h11
  -- We need to get the right conjuct of h12 based on <expert-advice>.
  let h13 := h12.right
  -- We need to get the left conjuct of h13 based on <expert-advice>.
  let h14 := h13.left
  -- False on the left can always be used.
  apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44014139294196772014353850839 : (((((((p1 ∨ ((p5 ∧ True) ∧ p4)) ∨ ((p4 → p2) → p3)) ∧ p5) → (((p2 → True) ∨ p3) ∨ (p3 ∨ False))) → (p5 ∨ p2)) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57466108708743135702504109886 : (((True → (p3 ∨ p1)) ∨ ((p1 ∨ (((p4 ∨ p1) ∨ False) → ((p1 ∨ True) ∧ p2))) ∨ (((((p1 → p4) ∧ p4) ∧ p4) ∨ True) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174429668945414991932374584565 : (((p1 → (False → (p4 ∨ ((p4 ∧ p1) ∧ p2)))) ∨ ((p1 ∨ (p1 ∨ p4)) ∨ False)) → (((p1 → True) ∧ p3) ∨ (p5 ∨ ((p3 ∧ p1) → True)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h7
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h10
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h12
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h13 =>
      -- False on the left can always be used.
      apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350018625755081949042110680520 : (p4 → ((((((p1 ∨ ((((p2 ∨ ((p2 ∨ False) ∨ p1)) ∨ p5) ∨ p5) → p5)) ∧ p3) → (p4 ∧ ((p4 ∨ False) → p3))) ∨ True) → p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66174356226129463438991203878 : ((p5 ∨ (((p1 ∨ p4) → ((((False ∨ False) → (True ∨ True)) ∧ (True ∧ False)) ∨ (((p3 ∧ False) ∧ p1) ∨ False))) → (p2 ∨ (p2 ∨ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657252448382421262129341262141 : (((((p4 ∨ (p1 ∨ p4)) → (p1 → ((p3 ∨ p3) ∨ ((p3 ∧ (p5 ∧ p1)) ∨ (p4 → ((p1 ∧ p4) → (p3 → True))))))) ∨ (p1 ∧ p5)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- Implications on the right can always be decomposed.
      intro h10
      -- Implications on the right can always be decomposed.
      intro h11
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- Implications on the right can always be decomposed.
      intro h14
      -- Implications on the right can always be decomposed.
      intro h15
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_127360184707585217609565652196 : ((p2 ∨ (False → ((p2 ∧ ((p2 ∨ ((p3 → (p2 → ((p5 ∧ p3) ∧ ((p1 ∧ (True → p1)) ∨ p5)))) ∨ False)) → True)) ∧ p5))) → (p5 ∨ True)) := by
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
theorem thm_5_vars_218800231312949285733319265423 : ((p1 ∧ (True ∨ (p5 → False))) → (((p4 ∨ ((p4 → ((p3 ∨ (p1 ∨ p3)) → (p1 → p1))) → p2)) ∨ ((True ∧ (p1 ∨ p1)) ∨ p5)) ∧ p1)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624800169818489227520591598482 : ((((p5 ∨ (((((False → False) ∨ ((False ∧ ((p3 ∧ (p4 → True)) ∨ (p5 ∧ False))) ∧ p5)) ∨ (p4 → True)) ∧ (p3 ∧ p2)) → p4)) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206694943275688017191840604204 : ((p2 → (p4 ∧ (True ∨ (False ∨ p5)))) ∨ ((((p4 → ((p5 → (p5 → p1)) ∧ ((p1 ∨ p1) ∧ p5))) → False) → (p3 ∨ (p4 → False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166400907034153495779707515068 : ((False ∨ (p2 ∨ ((True ∧ (((False ∧ (p1 → p2)) ∨ ((p3 ∨ p4) → p4)) → p5)) → p4))) ∨ (((p2 ∨ (True ∨ p5)) → False) → (False ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 ∨ (True ∨ p5)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208380813426696959466320771344 : (((p3 ∧ p2) ∨ ((p2 ∨ p2) ∧ p5)) → (((p2 → (p2 ∧ p5)) → (((p3 ∨ (p1 ∧ ((p5 ∧ p3) ∧ p1))) ∧ False) ∨ p2)) ∨ (p5 ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h8
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h8
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46846443486885486904079156215 : (((((p4 → (p2 ∧ p1)) ∧ ((p1 ∧ (((p1 ∧ (((p1 ∧ True) ∧ p2) → p5)) → (p5 ∧ p3)) ∧ p5)) ∧ p2)) ∧ False) ∨ (p2 → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139080951549747548398823226775 : ((((((p2 → p4) ∧ (p4 → ((False ∧ False) ∧ ((p1 → p5) ∨ p4)))) → (p1 ∨ (p3 ∨ p2))) ∨ (p5 ∧ p3)) ∨ p1) → (p5 → (p4 ∨ p5))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709286264127832969766095749296 : (((((p5 → False) ∨ (p1 → (p3 ∧ (p3 ∧ True)))) → ((((True → (p1 ∧ p4)) → p2) ∨ True) ∨ (p1 ∨ (p3 ∧ (p4 → (p3 → False)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114464615276958038476339182935 : (((((True → True) → ((p5 ∧ (((p3 ∨ p2) ∨ ((p3 → True) → p5)) ∨ p3)) ∨ p3)) ∨ p2) → ((p3 ∨ p4) → (p4 ∨ p1))) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346893962406299678058874017672 : (p3 → ((((((p5 → p1) ∧ p3) ∧ True) → ((p2 ∨ ((p1 → p3) ∨ p1)) ∧ (p5 ∧ True))) ∧ p1) ∨ (False ∨ ((True ∧ (p3 ∨ p2)) → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680369854598933969204681621493 : ((((((p2 ∧ (p2 ∨ ((p5 → p4) ∨ False))) → ((p1 ∧ True) → (p4 ∨ True))) → (p1 ∨ (p2 ∨ p2))) → ((p3 ∧ True) ∨ (p3 ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147881822175705848812673824492 : (((p5 → (p3 → (((p5 ∧ (p4 ∨ p1)) ∧ ((((p3 ∧ p1) ∨ (p3 → p3)) ∧ p5) ∧ p3)) ∨ p1))) → p4) ∨ ((p4 ∧ (p4 → p3)) → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159043381964636733431389418791 : ((p5 ∨ ((((False ∨ (True ∧ ((p2 → False) ∨ (p3 → (p2 ∨ p2))))) → (p1 ∨ p3)) ∧ p2) ∨ False)) ∨ (((False ∧ p1) ∨ p2) → (False → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46894766830269585511058128172 : (((((((((False ∨ ((p4 ∨ p4) ∧ True)) → p5) → False) ∧ p2) ∧ ((p5 ∧ p1) ∨ (False ∨ (False ∨ True)))) → p4) ∨ p2) ∨ (p4 ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301430390450904010439081248322 : (False ∨ (((True ∨ p2) → (False ∧ p1)) → ((p5 ∨ ((((((((p5 ∨ p2) ∧ p5) ∨ p2) → p2) ∧ p4) → (False ∧ p4)) ∧ p1) → p2)) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207643527476793850218787122224 : ((((p1 ∨ p2) ∧ (p4 ∨ p1)) → p1) → ((True ∧ ((p3 ∨ ((p2 → (((True → p4) ∧ p3) ∧ (True ∨ p3))) → (p1 ∨ p5))) ∧ p3)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_211702915621104318945541580079 : ((True ∧ ((p2 ∧ p3) → p3)) ∧ (((p4 → (p2 ∨ ((((p3 → ((False ∨ p4) → True)) ∧ p4) → p5) ∨ (p2 ∧ p2)))) → p4) ∨ (p2 → p2))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244527279660842384556248005007 : ((False ∧ p3) ∨ ((p4 → False) ∨ ((True → ((((p4 ∧ (p3 → p1)) ∧ p5) ∨ False) ∧ (p2 ∨ p1))) → ((p1 → ((p3 ∧ p1) ∨ p1)) ∧ p4)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41732206115488144013845934910 : (((((p3 ∧ p4) → (p3 ∧ p3)) ∧ (((p2 ∨ (p5 ∨ False)) → (p2 ∧ (False → p4))) ∧ (((p3 ∧ (True ∨ False)) → p5) → p2))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173084773365182213235037623021 : ((p1 ∨ (((((p4 ∨ False) → (False ∧ p2)) → p3) ∨ (p5 ∨ True)) ∨ (True ∧ p4))) ∨ (p3 → (p3 ∨ (((p1 ∧ (True → p4)) ∧ True) → False)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_315475024546410946791635365554 : (p3 ∨ (((True ∧ p5) → p3) → ((((p3 ∨ ((p5 → True) → ((p2 ∧ (False ∨ (True ∧ p1))) ∧ p5))) → p4) ∨ (False ∨ (True ∨ p4))) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_166552454291000125010094986723 : ((p5 ∨ ((True → ((p5 → (p2 ∧ p2)) → p3)) → (True ∧ (((True ∨ p4) → p1) ∨ p2)))) ∨ ((p4 ∧ ((True ∧ p1) ∧ True)) → (p1 ∨ False))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695055947970829330385100035617 : (((((p3 ∨ (((False → p2) → False) → (((p1 ∨ p3) ∨ p4) ∨ p1))) ∧ True) → ((True ∧ (p2 → p4)) → (p1 ∧ (True → (p1 → p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42316730431999408887686309013 : (((p2 ∧ ((p2 ∨ p1) → (((p5 ∨ False) ∧ ((p3 → ((False ∨ (p2 ∧ (p2 ∧ (False ∧ (p5 ∨ True))))) ∨ False)) → p5)) → p4))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229000571186707376549158132968 : ((p5 ∨ (p1 ∧ p3)) ∨ ((p4 ∨ p3) ∨ (True ∨ ((p1 ∧ False) → (p3 ∧ (((p2 ∨ (p4 ∧ True)) ∧ (p2 → (p2 ∧ (p1 → True)))) ∨ p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134221944646445372209960809386 : ((((((p3 → p3) → (p2 → p3)) ∨ p5) ∨ (p4 ∧ ((p5 → (p2 ∧ ((True ∧ (p1 → False)) ∨ p4))) ∨ p1))) ∨ p4) ∨ (False → (False ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173958368592873242895566101272 : (((((p1 → p5) → ((False → p2) ∧ p2)) → (((p3 ∧ p5) ∨ p1) ∨ p2)) → p1) → (((p3 ∧ True) → (p4 ∧ (p5 ∨ p5))) ∨ (p2 → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323211979466316454734968147787 : (p5 ∨ (((p2 ∧ (p4 ∨ (p5 → ((((p5 → (p1 ∧ (p4 ∨ True))) ∨ p3) ∨ (True → p5)) ∧ p1)))) → ((p5 ∨ p3) ∨ True)) ∨ (p4 ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_603528843132388614932139534571 : ((((p3 ∨ (((p5 → p3) ∧ p1) ∨ ((((p1 → p1) → p4) ∧ (p3 ∨ ((p5 ∨ (((False ∨ p2) ∧ p5) ∧ False)) ∧ p2))) → p3))) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157139737180768179150465415421 : ((((p5 → ((True → (((True ∨ p3) ∨ (False ∨ p5)) ∧ (p1 ∨ (p4 → p4)))) → True)) ∧ p2) → p5) ∨ (p1 ∨ (p2 ∨ (True ∨ (p4 ∨ p3))))) := by
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
theorem thm_5_vars_205626279300292242944428159913 : (((p2 ∧ False) ∨ (p5 ∨ (p3 ∨ p1))) ∨ (((((((((False ∨ (p5 → p2)) ∧ (False ∧ p5)) ∨ p5) ∧ p4) ∨ p5) ∨ p5) → p2) ∧ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622310554825144455749016483771 : ((((p3 ∧ ((True → (((p3 ∧ (p4 → ((p5 ∧ False) ∧ p5))) ∨ ((True → (True → p2)) ∨ (p1 → True))) ∧ (p3 ∨ True))) ∨ False)) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167896499072531690747112190357 : ((((((p3 ∧ p4) ∨ (p4 → False)) ∧ p4) → False) ∧ ((False ∨ (False ∨ (False ∨ p5))) ∧ True)) → ((p1 → ((False → (p1 ∨ p4)) ∧ p3)) ∨ True)) := by
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
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- False on the left can always be used.
        apply False.elim h10
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160849757733778440558478581187 : (((((False ∨ True) ∨ False) → p3) ∧ (((True ∨ (False ∨ p3)) → False) → (p2 ∧ ((False ∨ p5) → p5)))) → (((p3 → p5) ∧ (p5 ∧ p5)) ∨ True)) := by
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
theorem thm_5_vars_319372641938297732906828360231 : (p4 ∨ (((p2 ∧ (p5 ∧ p4)) ∧ (p1 → (p2 ∧ ((False → (p4 ∧ p1)) → p3)))) ∨ (p5 ∨ ((p1 → (True → ((False → p4) ∨ p3))) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140495908110459219216741816385 : ((((((p2 → p5) ∧ (True ∧ (p1 → (p1 ∧ False)))) → p4) ∧ ((p3 ∧ p4) ∧ p3)) ∧ (((p2 ∧ p1) ∨ p2) ∧ p1)) → (p5 ∨ (False → p5))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h3.left
  let h11 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h15
    -- False on the left can always be used.
    apply False.elim h15
  case inr h16 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h17
    -- False on the left can always be used.
    apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_810267737587474131838117849821 : (((p5 → ((((((p4 → True) ∧ ((p5 ∧ p1) ∨ p2)) → p2) ∧ p1) → False) ∧ (((p4 ∧ p1) ∨ p2) ∧ (True ∧ ((p1 ∨ False) → p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_790941036880856257798058085219 : (((p5 ∨ (p4 → (True → ((((((((p3 → p5) → p1) ∧ p4) ∧ p2) ∧ ((p4 ∨ ((p5 → False) ∨ p3)) → True)) ∨ p1) ∨ p5) → p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_740858715621409900254292216769 : ((((p3 ∨ False) ∨ (p2 → (((p5 ∨ False) ∨ (((p2 ∨ p3) → ((p4 ∨ p5) → False)) → ((p2 ∧ False) ∨ p3))) ∨ (p2 ∧ (p4 → p4))))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611662543204933594582191872294 : (((((p3 ∨ ((p1 → p2) → ((p2 ∧ (p4 ∧ (True ∨ p4))) ∧ ((p5 → (p1 ∧ (((p5 → p5) → True) ∧ p1))) ∨ p4)))) → p5) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48459568932241405954844475276 : ((((((False ∨ (False → p3)) ∧ (((p4 ∨ True) → False) → ((p4 ∧ p3) ∧ ((p2 ∨ p4) ∨ p2)))) ∨ p1) ∧ p3) ∧ (p4 → (p4 ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181179691065998015672772142888 : ((p1 ∧ ((True → ((p1 ∧ False) ∨ True)) → (((p1 ∨ p3) → p4) ∧ False))) → ((((p1 → (False ∧ p1)) ∧ (p3 ∨ p4)) ∧ (p1 → p2)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (True → ((p1 ∧ False) ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352827462099353115995700034660 : (p4 → ((False → p3) → (True → (p2 ∨ (((p1 ∧ False) ∨ (((True ∨ False) → (((p2 ∧ p1) ∧ (p4 → p3)) ∨ p4)) ∨ p5)) ∨ (p5 ∨ p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205285502828128026312045512097 : (((p1 ∧ (p1 ∧ p1)) ∨ (p2 ∨ p2)) ∨ ((p5 ∧ (p5 ∨ (True ∨ p4))) → (((p2 ∨ ((p3 ∨ p1) ∧ p5)) → (False → (p1 ∨ p1))) ∧ True))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148720213910564333668277285992 : (((p1 ∧ ((False ∧ False) ∨ (p1 ∧ (p1 → p5)))) → (((p2 → p3) ∧ (p4 ∧ ((False → p1) ∨ p1))) → p3)) ∨ ((p4 → (p3 → True)) ∨ p2)) := by
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
theorem thm_5_vars_48639099523018957011911390973 : (((((((True → False) → True) ∧ (True → p2)) ∧ (((p2 ∧ (p5 ∧ p3)) ∨ p1) → p1)) → ((p4 ∧ True) ∧ False)) ∧ ((False ∧ False) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69368805335164039083486709602 : ((p5 → (True → ((False ∧ (p5 ∨ (True ∧ ((p3 ∨ (p2 ∨ (p3 → p5))) → (p1 ∧ (((True → (p3 ∧ p2)) ∧ True) ∧ False)))))) ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172446177681420754242536256102 : (((((False → p2) ∧ p3) → p4) ∨ (p1 ∨ (((p1 → p5) ∧ p4) → (p5 → p5)))) ∨ (((p3 ∧ p5) → (p1 → (p5 ∨ p2))) → (p1 ∧ p5))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209146010412425969134312199027 : ((p3 ∨ ((p3 ∨ (p4 ∨ p3)) → False)) → (((((False → (p4 ∨ p2)) ∨ (p1 ∧ ((((False ∨ p2) ∧ p5) → p3) ∧ False))) → p5) → p5) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : ((False → (p4 ∨ p2)) ∨ (p1 ∧ ((((False ∨ p2) ∧ p5) → p3) ∧ False))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h5
      -- False on the left can always be used.
      apply False.elim h5
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h4
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h8 : ((False → (p4 ∨ p2)) ∨ (p1 ∧ ((((False ∨ p2) ∧ p5) → p3) ∧ False))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h9
      -- False on the left can always be used.
      apply False.elim h9
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h10 := h2 h8
    -- One of the premise coincides with the conclusion.
    exact h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216946872016118457671914343904 : (((False → (p5 → p2)) ∧ p1) → (p4 → ((((False ∨ ((p2 ∧ (False ∧ p2)) → p4)) ∧ ((((False → True) ∧ p4) ∧ p2) ∨ False)) → p5) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345584217436686949774059717186 : (p3 → (((p4 ∨ (False ∧ True)) → (((p2 → ((((p2 → p5) ∧ False) ∧ (False ∧ False)) ∨ (p4 → (p2 ∧ (False ∧ p5))))) ∧ False) ∨ p2)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356482401389687141634313494664 : (p5 → ((True ∨ (p5 → ((p2 ∨ (p1 ∨ (False ∨ True))) ∧ (p1 ∧ p5)))) → ((True ∧ (p4 ∨ (True ∧ p1))) ∨ ((True → (p5 ∧ False)) → p4)))) := by
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
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h11 := h9 h10
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39151551719943282891140008510 : ((((p1 ∨ False) → (((p5 ∧ True) → (((((True ∨ p2) ∧ (p2 ∨ (p2 ∧ p4))) ∨ p1) ∧ ((True ∨ True) ∧ p4)) ∧ p1)) ∧ p5)) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_661612344375160461881647991487 : (((((((p3 ∨ (True ∨ ((p5 ∨ ((p3 ∧ p1) ∧ p3)) → p3))) ∧ ((p3 ∨ p5) ∨ p4)) ∨ False) → ((p2 ∨ p3) ∧ p1)) → (p5 ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_487017294358695630331449944660 : (((((((False ∨ p3) ∧ True) ∧ p3) ∧ p3) → (((False → p5) → (p5 ∧ ((p1 → True) → False))) ∨ (p2 → (p3 ∨ ((True → p3) ∨ p3))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137217344335013576754559553429 : ((p1 ∧ (((p5 ∨ p3) ∨ (p4 → ((((p5 ∨ p1) ∧ (((False ∨ (p1 ∨ False)) → p3) → p1)) → p2) ∧ p3))) ∧ p2)) ∨ ((p3 ∧ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_797073424949421239338953625125 : (((p1 → ((((p3 ∧ p5) ∧ (p1 ∨ (True ∨ ((p3 → p2) ∨ p1)))) ∨ (((p2 ∨ (p1 → p4)) → False) ∨ ((p2 → p4) ∨ p4))) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113413929032323060898520586660 : ((((((((False → ((False ∨ False) ∧ p4)) ∧ (p2 → (False ∨ (p5 ∨ p1)))) ∨ p3) ∧ p2) ∨ (p5 ∨ True)) ∧ p4) ∨ (p3 → True)) ∨ (p5 ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342348910858645051391575242974 : (p2 → ((((p1 ∧ True) ∨ (((p3 ∨ ((p3 → p1) ∨ (p5 → p4))) ∨ p5) ∨ p2)) ∨ False) ∧ ((p1 ∧ p1) ∨ (p1 ∨ ((p2 ∨ p2) → p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_604110500760902211305003143922 : ((((p5 ∨ (True ∧ ((((True → p2) ∨ ((((p1 ∧ p5) ∨ p2) → (p1 ∨ (p4 ∨ p4))) → (p4 ∧ True))) → False) ∨ (p2 ∧ p1)))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305294130489469812009054154893 : (p1 ∨ ((((p4 ∧ p2) ∨ ((p2 ∨ (p1 ∧ ((p2 ∨ (p2 ∧ p3)) → (p4 ∨ True)))) ∧ p5)) → p4) ∨ (p2 ∨ (((p2 → True) → False) → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693854701781948922852862887116 : ((((((p5 → False) → (((True ∧ (p5 → (p4 ∧ False))) ∨ p4) ∨ p5)) → p1) ∨ ((p2 ∨ (((p2 → True) ∧ (p3 ∨ False)) → p3)) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620356456554241614858210188125 : (((((p2 ∨ p4) ∨ ((p4 → (((p3 → (False ∨ p1)) → p5) ∨ (p5 → (p5 → p2)))) ∨ (p3 → (True ∨ ((False ∨ p5) ∧ False))))) ∨ p2) ∨ p2) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244954787485008852202018764727 : ((p1 ∧ p3) ∨ (True ∧ (p2 ∨ ((((p2 ∧ False) ∨ True) → (p1 → p3)) → ((((p1 ∧ True) ∧ p4) ∧ p1) ∨ ((p2 ∧ False) ∨ (p1 → p1))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39416909581438543184752446648 : (((p4 ∧ ((p5 ∧ (p4 ∨ p5)) → ((((p3 → (p5 → True)) → p3) ∨ True) ∧ ((p5 ∧ (True ∨ p1)) ∧ (p4 ∧ (p1 ∧ p3)))))) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133967405107386305084304906996 : (((p5 → ((((p3 ∨ (p1 ∧ p3)) ∧ ((((p4 ∨ p2) → p4) ∨ (False ∨ p3)) ∧ p3)) ∧ (p1 → p1)) ∨ p3)) ∧ p2) ∨ (True ∨ (p5 ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250130395521759965106386086577 : ((True → p4) ∨ (p2 → (p2 ∧ (p5 ∨ (((((p3 ∨ (p5 ∨ ((p1 → (True → p3)) → (p3 ∨ p3)))) → p1) ∨ (p1 ∨ True)) ∧ False) ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168264860437618078215697749407 : (((p2 → (p2 → True)) → ((((p1 ∨ (p2 ∨ ((p2 → p1) ∧ True))) ∨ True) ∨ p1) → False)) → (((True ∨ (p4 → True)) → p3) ∨ (p4 ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 → (p2 → True)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : (((p1 ∨ (p2 ∨ ((p2 → p1) ∧ True))) ∨ True) ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38296289448926702180582437143 : ((((p4 → (((False ∧ p2) ∧ ((((p1 ∨ (True ∨ p3)) ∨ (p1 → p4)) ∧ True) → False)) ∨ True)) ∨ (p5 ∨ (p5 ∧ (p1 ∧ p2)))) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_786388259608113698744937532545 : (((p4 ∨ ((True → ((p5 ∨ p4) ∨ (((((p4 ∧ p3) → p3) ∨ (p3 ∨ False)) ∧ p1) ∨ p1))) → ((True → (p3 ∧ p4)) → (False ∨ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156988059988527838290368655534 : (((((p4 → (False → (True ∨ p5))) → p4) ∨ ((((p4 ∨ (p1 → p1)) → True) → p5) ∨ False)) ∨ p2) ∨ ((True ∨ True) ∨ ((p2 ∧ p4) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204867890826945870154904095802 : ((((p2 ∧ (p1 ∧ False)) → p2) → p5) ∨ (p2 ∨ (((((p2 ∨ (False ∨ p1)) → ((False ∨ True) ∨ (p1 → p2))) → False) → False) ∨ (True ∨ True)))) := by
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
theorem thm_5_vars_49029407751346490332056412022 : ((((((p5 ∨ p2) ∨ True) ∨ ((True → ((p1 ∧ True) ∨ True)) ∧ ((False ∧ p5) → (False → (p4 ∨ False))))) → p2) ∨ ((p5 ∨ p3) → True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49811146731392145488906764828 : (((p1 → (((((p2 ∧ p5) ∧ p4) → (((p4 → (p5 → p3)) ∧ (p2 ∧ (True ∨ p1))) ∨ p4)) ∧ p4) ∨ p3)) → ((p5 ∧ p4) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68402059387945375956063677197 : ((p3 → (((p5 ∧ p3) → True) → (((p4 ∧ True) ∨ (((p1 ∧ p1) → p2) ∨ (((p1 → p4) ∧ True) ∨ ((p3 ∧ p4) → p2)))) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783286144819169765742124523367 : (((p3 ∨ ((((p3 → ((False ∧ p1) ∧ (p3 → p3))) ∧ (p1 ∨ ((p5 ∨ True) ∨ p5))) ∧ (p3 ∧ p1)) ∨ (((p4 → False) → True) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158303624322212223109249123339 : ((((p4 → False) → p2) → ((p4 ∨ (((True ∧ False) → (p2 ∨ (p3 ∧ p5))) → p1)) → (p4 → p1))) ∨ (True ∨ (((p4 ∧ p2) ∧ False) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255020010961430858496043444224 : ((p4 ∧ p1) → ((((((p3 ∨ p3) ∧ p2) ∧ p5) → ((p5 ∨ (p5 ∧ p4)) → p4)) ∧ p2) → (((p1 → (p2 → (p3 ∧ p4))) ∧ True) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149503885071418847187574722100 : ((p1 ∧ (((((p5 ∨ (p1 ∧ p4)) → ((p2 ∨ p5) ∨ p2)) ∨ p5) → (p3 ∨ p2)) → ((p2 ∨ p5) → p1))) ∨ (False → (p5 ∧ (p3 → True)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_76497779470174437946374352848 : ((((p2 ∨ (((True ∨ (p4 → (True → p4))) → (False ∧ p4)) ∨ (((p5 → p1) → (p3 ∨ False)) ∧ True))) ∨ ((p4 → True) ∧ True)) → p4) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p2 ∨ (((True ∨ (p4 → (True → p4))) → (False ∧ p4)) ∨ (((p5 → p1) → (p3 ∨ False)) ∧ True))) ∨ ((p4 → True) ∧ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112446681779358139123438456439 : (((((True ∨ ((p5 → p2) → (p5 ∧ ((p3 ∧ (p5 → (((p3 ∨ p1) → p2) ∧ p3))) ∧ (True → True))))) → p5) ∨ p4) → False) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153430473559447576042344813209 : ((p4 ∨ (((p4 → ((p5 ∧ (False → (p5 ∧ False))) → p3)) → ((p1 ∨ p2) ∧ (p5 ∧ (False ∧ True)))) ∨ True)) → (p2 ∨ (False ∨ (False → False)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228649007768588336580452782379 : ((p2 ∨ (p2 ∧ False)) ∨ ((((((p4 ∧ (((False ∨ p5) ∨ p4) ∧ False)) ∧ (p1 ∨ (p5 ∨ p3))) → p3) → False) ∨ (p1 ∨ (True ∨ p5))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



