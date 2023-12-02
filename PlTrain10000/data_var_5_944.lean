variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110883974681536071615131606224 : ((((((False ∧ ((True ∨ (p2 ∧ p1)) ∨ p2)) ∨ (((p2 ∧ p5) → False) ∧ p2)) → ((p2 → (p5 → p1)) ∧ p1)) → p1) ∧ True) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47294781460579543091704813647 : (((((p4 ∧ p3) ∨ p1) ∧ (((False ∧ ((p3 ∨ p4) → False)) ∨ (p2 → p4)) → ((((p5 ∧ p4) → p5) → p4) ∧ False))) ∨ (True ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47336847566404510101969992081 : ((((True ∨ True) ∧ ((p5 ∨ ((((True → (True ∧ p4)) ∨ False) ∨ False) → ((False ∨ (p5 → False)) ∧ p4))) → (p2 ∧ p5))) ∨ (p3 → True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54946051621450730857503456384 : ((((p2 ∧ (p1 ∧ True)) ∧ (p1 ∧ True)) ∧ (False ∧ (p3 → (((((True → p5) ∧ ((p3 ∨ True) ∧ (p5 ∧ True))) → True) ∧ True) → p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55643469564605579521969216651 : (((((p1 → p4) ∨ p5) ∧ p2) ∧ (((p2 → True) ∨ p2) ∧ (((p3 ∨ ((False → ((p3 ∨ p4) → p4)) ∧ p1)) ∧ p4) ∧ (p3 ∧ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51286444896366392608653196145 : (((p3 ∧ (((((True ∧ (p3 ∧ p2)) ∨ True) → False) ∧ p2) → ((True → p5) → (p1 ∧ False)))) ∨ (p5 → ((p5 ∧ (p3 ∨ p2)) ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64815802539353281196032291865 : ((p2 ∨ ((((p5 → (p5 ∨ p2)) → (((p5 ∧ (p2 ∨ ((p1 → False) → ((False → p4) ∧ p3)))) ∧ (True → p4)) → False)) ∨ True) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355217981825756332025480480893 : (p5 → (((((p4 → (p2 ∨ p2)) ∧ p4) ∨ p2) ∨ (True → (((((p2 ∨ p4) ∨ True) ∧ True) ∧ False) ∧ (((p4 ∧ p3) → p2) ∨ True)))) → p2)) := by
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
      let h5 := h4.left
      let h6 := h4.right
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h7 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h8 := h5 h7
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h10 =>
        -- One of the premise coincides with the conclusion.
        exact h10
    case inr h11 =>
      -- One of the premise coincides with the conclusion.
      exact h11
  case inr h12 =>
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h13 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h14 := h12 h13
    -- We need to get the left conjuct of h14 based on <expert-advice>.
    let h15 := h14.left
    -- We need to get the right conjuct of h15 based on <expert-advice>.
    let h16 := h15.right
    -- False on the left can always be used.
    apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306656356991591200842597918952 : (p1 ∨ (True ∧ ((((p3 ∨ p2) ∨ ((p3 ∧ False) ∧ (p1 → (True ∧ p4)))) ∨ p3) ∨ (((p4 ∧ ((p3 ∨ p1) ∨ (p5 → p2))) ∧ p1) → p4)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50584945671166238056507006308 : ((((p3 ∨ ((p3 → (((p5 ∧ (p3 ∨ ((p2 ∧ False) → p3))) → (p3 ∨ p5)) ∧ p1)) ∧ p2)) → p5) → ((p2 → p3) ∨ (p2 → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300415686252157205644371506273 : (False ∨ ((p3 → (((False ∧ p3) → (True ∧ p1)) → (((False → (p4 → (p5 ∧ (p3 ∨ p4)))) ∧ p3) ∧ (p1 ∨ p4)))) ∨ ((p5 ∧ False) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346921670594486062622645709421 : (p3 → ((p5 ∧ ((True ∨ ((p5 ∨ (p3 ∨ ((p1 ∨ p3) ∨ p3))) ∨ ((p1 ∨ True) ∨ p2))) ∧ p1)) ∨ ((((p2 ∧ p1) ∨ True) → False) → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((p2 ∧ p1) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_74513821970127412269469947949 : ((((p1 → True) → (((((True ∨ p1) → False) → True) ∨ ((p2 → (True → (p1 ∧ ((False ∧ p4) ∧ (True → p4))))) ∨ p4)) ∧ False)) ∨ p3) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : (p1 → True) := by
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
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245665926272514882830614051206 : ((p3 ∧ p1) ∨ ((((p4 ∨ ((False → p2) ∧ p2)) → False) ∧ ((True ∧ ((p1 ∧ p3) ∧ p1)) → p5)) ∨ (False → (False ∧ ((p1 ∧ True) ∧ p2))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809994057733116969902001383606 : (((p5 → ((((((p5 → (p1 ∧ p3)) ∨ p5) ∨ (p2 ∨ False)) ∨ (False ∧ (((p5 ∨ p4) ∧ p1) ∨ p2))) → p5) → (p2 ∧ (True ∨ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_20848132272461959569112438486 : (((((p2 → (p1 ∧ True)) → (p2 ∨ p1)) ∧ ((p2 ∧ p5) ∧ p4)) ∨ (False → ((p1 ∨ (False ∧ ((p4 ∧ p2) → p1))) ∧ (p4 ∨ p5)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_805024881747044561375024883785 : (((p3 → ((p2 → p5) → ((False ∨ ((True ∧ p1) ∨ (p5 → False))) ∨ ((False ∨ (((((p3 → False) ∨ p3) ∨ p1) → p3) → p4)) ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617385729672560274197524736074 : ((((((False → p5) → ((p2 ∨ False) ∨ (p4 ∧ p5))) → ((((p2 ∧ p3) → (False ∨ (p2 ∧ ((p1 → p3) ∧ p1)))) → p2) ∧ p4)) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621135415969494172630087504041 : (((((p5 → True) → (((True ∨ (p4 ∧ p1)) → ((p2 ∧ (p1 ∧ False)) ∨ p5)) → (((p2 → (p3 ∧ (p1 ∨ p5))) ∨ p5) ∧ p2))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783630265691062244555854535096 : (((p3 ∨ (((((True ∨ (p5 → False)) → p3) ∨ p3) ∧ p1) ∨ (p4 → (False ∨ (((((p4 ∧ p3) → (p5 → p2)) ∧ True) → p1) ∧ True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158138989560973081017419524079 : ((((p1 → (p5 → False)) → p5) ∨ (True ∧ ((False ∨ p3) ∨ (True ∧ (True ∨ (p5 ∨ (p3 → p4))))))) ∨ ((p5 ∨ p1) → (p2 → (p1 ∧ p1)))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168641323141920692334147455694 : ((p4 ∧ ((((False ∨ ((True → p5) → False)) ∨ ((False → p2) ∧ p5)) ∨ p3) ∨ (False → p1))) → ((True → (p1 → p2)) → ((p4 ∧ p2) → p2))) := by
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
  let h6 := h1.left
  let h7 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- False on the left can always be used.
          apply False.elim h11
        case inr h12 =>
          -- One of the premise coincides with the conclusion.
          exact h5
      case inr h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- One of the premise coincides with the conclusion.
        exact h5
    case inr h16 =>
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h17 =>
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62862545377073142763684234900 : ((p4 ∧ (((True → p1) ∨ p2) ∧ ((((((p4 ∧ p4) ∨ p3) ∨ p3) → ((p4 ∨ False) ∧ p5)) ∨ ((p5 ∧ (p4 → p1)) → p2)) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_33493620564949548701744448633 : ((p4 ∨ ((p4 → (False ∧ True)) → ((p1 ∧ ((((p4 ∨ p2) ∧ p1) → ((p2 ∨ p5) → p4)) → (p3 ∧ (p5 ∨ (p2 ∨ False))))) ∨ True))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_314243302683181034928581359388 : (p3 ∨ (((((((True ∨ True) → p2) → (p5 ∧ (False → (p4 → (False ∨ (p3 ∧ False)))))) ∨ False) ∨ p2) → (False ∨ p1)) ∨ (False → (p5 ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159479662501447187457873253288 : ((((((p3 ∨ p5) ∨ True) → p3) ∧ (((p5 ∧ p5) → ((p2 ∨ (True → p1)) ∨ True)) ∨ p5)) ∧ p5) → (((p2 ∨ (p4 → True)) → p4) ∨ True)) := by
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
theorem thm_5_vars_266025565510833851961204928299 : (True ∧ (p1 → ((p3 → ((p5 → p5) ∧ (True ∧ p5))) → (((p2 ∧ (p1 → ((p5 ∨ ((False ∧ (False ∨ p2)) → p2)) ∧ p4))) ∧ p1) ∨ p1)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67669315224255368245407481278 : ((p1 → (True → ((p5 ∨ ((((True ∨ (p3 → False)) → p1) → (((p1 ∧ True) → p3) ∨ p4)) → (p5 ∨ (p5 ∧ p4)))) ∨ (p1 → p1)))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_190936507033168615755703100465 : ((((p1 ∧ False) ∧ (p2 ∧ p2)) ∧ (p5 ∧ (p5 ∧ p3))) ∨ (False → (((p1 ∨ ((p1 ∨ (p3 → (p2 ∨ p2))) → (p4 ∧ p4))) ∨ p2) ∧ p2))) := by
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
theorem thm_5_vars_197115768414789706762656200769 : (((p1 ∨ ((p4 ∧ (p2 ∨ p5)) ∨ p3)) ∨ p3) ∨ ((((p3 → p5) ∧ p4) → ((((p4 ∧ (False ∨ False)) → True) ∧ (p2 → p3)) ∧ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_681082666715599560945560481741 : ((((True ∧ ((p4 → ((True ∧ ((p3 ∧ (True → p5)) ∨ False)) ∧ p4)) ∧ (p5 ∨ (p1 → (p5 ∨ True))))) → (p3 ∧ ((p1 → p1) ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611157856140556484920671995029 : (((((((p2 ∨ p2) ∨ False) ∨ (((((p3 → True) ∧ ((True → p2) ∨ p2)) ∧ p5) ∧ (p2 ∨ ((p4 ∨ p5) → p2))) ∨ p5)) → p3) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244718672158727805087426486431 : ((p1 ∧ True) ∨ (p1 ∨ ((p5 ∨ ((((False → p5) → p4) ∧ (((True → ((p5 → p4) ∧ False)) → (p1 → p2)) → p4)) → False)) ∨ (p2 ∨ True)))) := by
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
theorem thm_5_vars_352507156573175971443264636259 : (p4 → ((True ∧ p4) ∧ ((p2 → ((p2 ∧ (((p1 ∨ p5) ∧ p5) ∨ p1)) ∨ (False ∧ (((p1 → p5) ∨ (p4 ∨ (p1 ∨ p3))) ∨ p4)))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_88756752815102046150796282128 : ((((False ∧ (p3 → p1)) → p1) → ((((True → ((p3 ∨ p5) ∧ p4)) ∧ ((p2 ∧ p5) → (True → p5))) ∨ (True → False)) ∧ (True ∧ p2))) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False ∧ (p3 → p1)) → p1) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h11 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h12 := h9 h11
    -- We need to get the right conjuct of h12 based on <expert-advice>.
    let h13 := h12.right
    -- One of the premise coincides with the conclusion.
    exact h13
  case inr h14 =>
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h15 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h16 := h14 h15
    -- False on the left can always be used.
    apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_586128623125224812048915994285 : ((((((((p5 ∨ ((False → p2) ∧ ((False ∨ p2) ∨ p4))) → (p1 ∨ p1)) ∧ p5) ∧ (p5 ∨ (p1 ∨ (p1 → (p1 ∧ True))))) ∧ p2) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_802262397680401810129832656536 : (((p2 → (p4 ∧ ((((False ∨ ((p2 → True) ∧ (False ∧ p4))) ∨ (p4 ∧ ((p3 ∧ False) ∨ p4))) ∧ (p5 ∨ ((p1 ∧ False) ∨ p1))) ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56691671639558135242738987402 : ((((True ∧ p4) ∨ p4) ∧ (((((p3 ∨ False) ∧ (((p1 ∨ (p5 ∧ p2)) ∧ ((True → True) ∧ (p1 ∧ False))) → True)) ∨ True) → p3) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302725433858966113768880116755 : (False ∨ (p3 ∨ (p4 ∨ (((p1 ∨ (False → ((p3 ∧ (((False ∨ (True ∨ False)) ∧ p4) → ((p4 ∧ False) ∧ p4))) → p3))) → (p3 ∧ True)) → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 ∨ (False → ((p3 ∧ (((False ∨ (True ∨ False)) ∧ p4) → ((p4 ∧ False) ∧ p4))) → p3))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h2
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38043017500501238188252062340 : ((((((((p4 → p2) → ((p1 ∧ p5) ∨ ((True → (p2 ∨ p3)) ∧ p2))) ∨ ((True ∨ p5) → p2)) → False) → p5) → (p1 ∨ False)) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159248979036533354749870087389 : ((p3 → ((p1 ∧ (p1 ∨ False)) ∨ ((((p1 ∨ ((False → p5) ∧ p4)) → p3) ∨ False) → (p1 → False)))) ∨ ((p3 ∨ p1) ∨ ((True ∨ p3) ∨ p5))) := by
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
theorem thm_5_vars_613435276540672136589920784518 : (((((p1 ∨ (((p4 ∨ ((p5 → (p2 ∧ (True → False))) ∨ (((p1 → p3) ∧ p4) ∧ p1))) → (False ∧ p3)) ∨ p2)) → (p1 → False)) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_768664370912004581542743594477 : (((p5 ∧ ((p1 → (((p2 → (p1 ∨ (p5 ∨ p5))) ∨ p3) ∧ (True ∨ True))) → ((((True → True) ∧ (p3 → p1)) → p5) ∨ (True → True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40314494194067779294917591898 : ((((((p5 ∧ p3) ∨ (p3 ∨ ((p3 ∧ ((((p5 → p4) ∨ True) ∨ False) ∨ ((p5 → p3) ∨ p1))) ∧ (p4 ∨ p2)))) ∧ p1) ∨ False) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318658934758486023388416410541 : (p4 ∨ ((p5 → ((((p3 ∨ p2) → ((False ∨ p2) ∨ p2)) → p2) → (p2 ∧ ((p2 → ((p1 ∧ (p4 → False)) → False)) ∧ p1)))) ∨ (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_722010910536219083454771890696 : ((((False → (p5 ∧ (p1 ∨ p3))) → (((p2 → (True ∧ (False ∨ (p2 → False)))) → ((False ∨ True) ∧ p4)) ∧ (p4 ∨ ((p2 → p5) ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137882475074102992311714956943 : ((p4 ∨ ((((((True ∨ p3) ∧ (p4 ∨ ((p4 → (True ∧ p3)) ∨ p3))) ∧ p5) → (True ∧ p4)) ∧ (p4 ∧ p2)) ∨ p2)) ∨ ((p3 → p4) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328790357201165166445967663735 : (True → (((((p2 ∧ False) ∧ (p4 ∧ p5)) ∧ p3) ∨ (p3 → p1)) ∨ ((((p1 ∧ p2) → (p5 ∨ p1)) ∨ True) ∨ (((False → p5) → p1) → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115034045187703792602270924898 : (((((p3 ∨ ((False ∧ False) ∨ (False → (True ∧ p2)))) ∧ False) ∧ p4) ∨ ((p5 ∨ (((p3 ∨ p3) ∨ p3) ∧ (p2 → p1))) ∧ p4)) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135133836864802633946645052627 : (((p5 ∧ ((((p3 ∨ ((False → p5) → p2)) ∨ (p1 ∨ p5)) ∧ (p1 → ((p2 ∧ p3) ∧ p2))) ∨ False)) ∨ (p3 → True)) ∨ ((False ∨ p3) ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738118003614160665703141358851 : ((((False ∧ p1) ∨ (((p3 ∧ p1) ∧ (p3 ∨ (p1 → (True ∧ (p3 ∧ (p5 ∨ ((((p3 ∨ p1) ∧ p1) ∨ p3) ∧ p1))))))) ∨ (p5 ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319175977932591306032510272136 : (p4 ∨ ((((True → False) ∨ p2) ∨ (False ∨ (True → (p4 → (False ∨ (p5 ∧ ((p2 → False) → False))))))) ∨ (True ∨ ((p2 → (p3 → p2)) → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166221552361864194252875595342 : ((p2 ∧ ((((p2 ∧ ((p5 ∧ (p3 ∧ (True → True))) ∨ True)) ∨ True) ∧ False) ∨ (p3 → True))) ∨ ((p4 → p4) ∨ (p1 ∨ ((True ∧ True) → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257710626680733107719802295754 : ((p3 ∨ p3) → (p3 ∧ ((((((True ∨ (((p4 ∧ p1) ∧ True) → (p5 ∨ p1))) ∧ (p5 → (p4 ∧ p2))) ∨ (p2 ∧ True)) → p1) ∨ p3) ∨ p2))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159010216346274782600678743220 : ((p4 ∨ ((((p3 → (((p5 → (p5 ∧ p3)) ∧ (p1 → p2)) → (True ∨ p4))) ∧ p5) → p4) → p5)) ∨ ((p3 ∧ p1) → (p5 → (p1 ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_70612585330346048822832566422 : (((((((p4 ∧ p5) ∨ p2) → (p2 → True)) → (((True → p5) ∨ ((p4 ∧ p1) ∧ p1)) ∧ p1)) ∧ (p3 → (p4 ∨ (p4 ∨ p3)))) ∧ p2) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : (((p4 ∧ p5) ∨ p2) → (p2 → True)) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h9 := h4 h6
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147845752332862768029709784690 : (((p4 ∨ (p2 ∨ (((((p2 ∧ p1) ∨ False) ∨ (p1 ∨ p1)) → p1) ∧ (p5 ∧ (p2 ∨ (p5 ∨ p5)))))) → p3) ∨ (p1 ∨ ((p1 → p5) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_650522527502384121755092810160 : (((((((p2 ∧ (True ∨ (p5 ∧ True))) → (p3 → False)) ∧ (p1 ∧ False)) ∨ (p2 → ((p4 → ((True → p2) → p1)) ∨ p2))) ∧ (False → p2)) ∨ p3) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357499486050404531102340238980 : (p5 → (True ∧ (((p4 → (((p4 ∧ ((p3 → (p1 → p2)) ∧ p3)) ∨ p1) → True)) → (((True → p5) → p1) ∨ (p1 → p1))) ∨ (False ∧ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731492992519870412924897780339 : ((((True → (p3 → p2)) → (p2 → ((((((((p4 → p2) → False) ∧ p5) ∨ p1) ∧ (True ∨ p2)) → ((True ∧ True) ∧ False)) → p1) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53430110530594677773302801706 : ((((((p5 ∧ p5) → p3) ∨ p5) ∨ ((p4 → (p2 → p5)) ∨ p3)) → ((((p1 → p5) ∨ ((p3 ∨ (p2 → True)) ∨ p5)) ∨ p4) ∨ True)) ∨ p5) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
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
theorem thm_5_vars_193936704289268176363000299706 : ((p2 ∨ ((p5 → (((p2 ∨ p2) ∧ p5) ∨ True)) ∧ True)) → (p4 → ((p2 ∧ (((True ∧ (True ∧ ((p4 → True) ∨ True))) ∧ False) ∧ False)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191586722147474668484694958421 : ((p2 ∧ (p1 ∧ (p5 ∧ (((p1 ∧ p4) ∧ p2) ∧ False)))) ∨ (p2 → ((p4 → (((p4 ∧ p4) ∨ ((p3 ∧ False) ∨ p4)) → p4)) ∨ (p3 ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_87278712965843677424220987961 : ((((((p4 → True) ∨ p1) → True) → False) ∧ ((p4 ∨ (((((p5 → (True ∧ False)) ∧ (p5 → (p4 ∧ False))) → p2) ∧ p4) ∧ p5)) → False)) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (((p4 → True) ∨ p1) → True) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_799437881666298256609065146 : ((False ∧ (((p1 ∨ (p3 ∨ ((((p1 ∧ (p3 ∧ p2)) → False) ∧ (False → p1)) → ((True → (p4 ∧ p4)) → p4)))) → False) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183149776048935257071909332990 : ((True ∧ ((((True ∨ True) → (p2 ∨ p5)) → p2) → (False → p2))) ∧ ((True → ((p3 ∧ ((p2 ∨ (p5 → p5)) → (p1 ∨ p1))) ∨ True)) ∧ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64447030439470057006249330926 : ((p1 ∨ (((True → ((p3 → (p5 ∧ (((p2 → (True ∧ p3)) ∧ (p4 ∨ ((p3 ∧ False) ∨ p1))) → p1))) → p2)) ∧ p5) → (p5 ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224356465990791287411672934388 : ((False → (p1 → p4)) ∧ ((((p2 ∧ (True → p3)) ∧ (p4 → (((p3 ∧ True) ∨ p3) ∧ False))) ∨ (p1 ∧ p3)) ∨ (p2 → (p2 ∨ (p3 ∨ False))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246236776486128660470590154804 : ((p4 ∧ p3) ∨ (p1 ∨ (((p4 ∧ p3) → ((((((p2 → (p2 → p1)) → (p5 ∨ False)) ∧ (p2 ∨ p4)) → (True ∨ False)) → p1) ∨ p4)) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_721990761990930176696029896496 : ((((False → ((p2 ∧ False) ∨ True)) → ((p3 ∨ p4) ∨ (p4 ∨ (p3 → (((True ∨ ((True → (p2 ∨ False)) → p3)) ∨ (p4 ∨ False)) → p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194152636716295036163635877131 : ((p1 → (p5 ∧ (((True ∧ (False ∨ p5)) ∧ p4) ∧ False))) → ((p5 ∧ (p5 ∧ ((p1 ∨ (p2 ∨ (True ∨ True))) → p4))) ∨ (True ∨ (p1 → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40069234406134300894286545359 : (((((p1 ∨ (p5 ∧ ((False ∧ (p3 ∨ p4)) ∨ (True → ((p4 ∧ p4) ∧ ((p3 → p5) ∨ (p5 ∧ (p1 ∧ False)))))))) ∨ False) ∧ True) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_80383216423017864382302909394 : ((((p5 ∧ (((p5 ∧ p1) ∧ False) ∧ ((p5 → (p4 ∧ p2)) ∨ p2))) ∨ (((p5 ∧ (p4 ∨ p5)) ∨ (True → p1)) ∨ True)) → (True → False)) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p5 ∧ (((p5 ∧ p1) ∧ False) ∧ ((p5 → (p4 ∧ p2)) ∨ p2))) ∨ (((p5 ∧ (p4 ∨ p5)) ∨ (True → p1)) ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738338135312507779783454328734 : ((((p1 ∧ True) ∨ (True → ((p3 ∨ False) ∨ ((((p1 → p2) ∧ ((p2 → (((p3 ∧ p3) ∧ (p4 ∧ p1)) ∨ False)) ∧ True)) ∨ p4) → p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337136955314427584697422461823 : (p1 → ((p3 ∨ (((((False ∨ False) ∨ p2) → p4) → (p2 → p5)) → ((p5 → (p3 ∧ False)) ∨ (p4 → ((p4 ∨ p2) → False))))) ∨ (p3 → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_799561863030755228766410302107 : (((p1 → (p4 ∨ (((p3 ∧ (p4 ∧ ((True ∧ p2) ∧ ((((p2 ∨ p2) ∨ p2) → p5) ∨ ((p5 ∧ p4) ∧ p3))))) ∨ (p2 → p2)) ∨ p4))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118663623480566020782320351198 : ((p4 ∨ (p3 ∨ ((False ∧ (False ∨ True)) ∧ (((((p2 → p2) ∨ (((p1 ∨ p2) ∧ (False ∧ p1)) ∧ False)) ∧ p4) ∨ False) ∨ p3)))) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328976207208162169453123831960 : (True → ((((p3 → (p2 → False)) → p1) ∧ p4) ∨ (((p4 ∨ p5) ∧ (p2 → p3)) ∨ (False ∨ (p5 ∨ ((True ∨ (False → (p3 ∧ p4))) ∨ True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_598839174085214616468610758720 : (((((p4 ∧ True) ∧ ((False ∨ (p5 ∨ ((p3 → p1) ∨ ((p2 → p4) ∨ (False ∨ p2))))) ∨ (((p5 ∨ p2) ∨ p4) → (p4 ∨ p2)))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53820279407605498435112450454 : ((((((p2 ∧ p4) → (p3 → p1)) → p5) ∨ (p3 ∨ False)) ∨ (p2 → (p1 → ((True ∧ p2) → (((p4 ∨ p4) ∨ (p3 → p2)) ∧ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349644156070562998289695540572 : (p4 → ((((((((p3 ∨ p5) ∧ p1) ∨ True) ∨ p3) ∨ True) ∧ (((p1 → p5) → (p2 ∧ (p2 → p5))) ∨ (p5 ∧ p2))) ∨ (p1 → p4)) ∧ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_755194356282022158114065902253 : (((False ∧ (p3 → (p2 → ((True ∧ (((p3 → p2) → False) ∧ (False ∨ False))) ∧ ((p1 ∨ p5) → (False ∧ (p2 ∧ ((p2 ∨ p1) ∧ False)))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113940302517486525448141261024 : ((((((p1 → (p1 ∧ p3)) ∨ p4) ∨ False) → ((p1 ∧ ((p4 → p4) ∨ (p3 ∧ (p2 → False)))) ∧ p1)) ∧ (p5 ∧ (p5 → False))) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253147181881403637951852703303 : ((True ∧ p5) → (((p5 ∧ True) ∨ p5) → (p2 → ((p1 ∧ (((p1 ∧ p3) ∨ ((p3 ∨ (False ∧ (p4 ∧ (True → True)))) ∧ p1)) ∨ p1)) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h1.left
    let h8 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h1.left
    let h11 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150225045223053428622735540170 : ((p2 → (p1 ∨ (((((p2 ∧ p1) ∧ False) → ((p2 ∨ p5) ∨ (False → p3))) ∨ False) → (p5 → (p3 → False))))) ∨ (True ∨ ((p3 → False) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149510335074018713632340381154 : ((p1 ∧ ((p4 ∨ ((p3 ∨ (p4 ∧ True)) ∧ p2)) → ((((p3 ∧ True) ∨ (p2 → (p3 ∨ p1))) ∧ True) → p1))) ∨ (True ∨ ((p4 ∧ True) → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192446626377594694247784809256 : ((((p3 ∨ ((True → (p2 ∧ p4)) ∧ False)) → p4) ∨ p5) → ((p2 ∨ p2) ∨ (((p1 ∨ (p5 → p5)) ∧ ((True → True) ∨ (p1 ∨ True))) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190107283009402858323857571069 : ((((True → ((p4 ∨ p3) ∨ p2)) → (p2 ∧ p2)) ∧ p1) ∨ (((p2 ∧ (False ∧ p3)) ∨ (True ∨ ((p1 → False) ∨ p2))) ∨ ((p4 → p1) ∧ p4))) := by
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
theorem thm_5_vars_63927236367639203503110913683 : ((False ∨ (((True → (((((False ∨ (p1 ∧ p5)) ∨ ((p1 → p1) ∧ True)) ∨ p1) → False) → (True ∧ ((p4 ∧ p5) ∨ p2)))) ∨ p2) ∨ p2)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (((False ∨ (p1 ∧ p5)) ∨ ((p1 → p1) ∧ True)) ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51031526169276043243476297065 : (((p5 ∧ ((((p1 ∧ p5) → (p1 ∧ (((p2 ∨ p2) ∧ p3) ∨ p2))) ∨ False) ∨ (p4 ∧ False))) ∧ ((p2 → True) ∨ (p2 ∧ (p3 ∨ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199538061575019273389342938289 : (((((p5 ∧ True) ∨ (True → p2)) ∧ p2) → False) → ((p2 ∧ (p3 → (p3 → (False ∨ (p3 → False))))) → (((p3 ∨ (p2 ∧ p2)) ∨ p1) ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h3
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : (((p5 ∧ True) ∨ (True → p2)) ∧ p2) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h5
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h7
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351326366273843663100216120967 : (p4 → ((False ∨ (((p5 ∧ True) ∧ (((p3 → p2) ∨ p2) ∧ True)) ∨ (((True ∨ (True ∨ False)) ∨ (p2 ∧ p1)) ∧ p4))) → ((False ∧ p1) ∨ True))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h7.left
      let h11 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
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
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h17 =>
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h18 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h19 =>
          -- Disjunctions on the left can always be decomposed.
          cases h19
          case inl h20 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h21 =>
            -- False on the left can always be used.
            apply False.elim h21
      case inr h22 =>
        -- Conjunctions on the left can always be decomposed.
        let h23 := h22.left
        let h24 := h22.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218621200323185695445120300594 : (((p5 → p5) → (p4 ∧ False)) → (p5 ∨ ((((p4 ∧ p4) → (((((p5 → p3) ∨ p4) → p5) → (p2 ∧ p2)) → (False ∧ True))) → p1) ∧ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 → p5) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327232481982521399995663419950 : (True → ((p3 → (p2 ∨ ((p4 ∧ (p2 → p2)) → ((((p2 → (True ∧ (p1 ∨ p2))) → ((p1 ∧ True) ∨ p5)) ∨ p4) ∨ (p2 ∨ p2))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209376033539922575512897394673 : ((p1 → (((p3 ∧ p1) ∨ p3) → False)) → ((p2 ∧ ((True ∧ (p3 ∧ p2)) ∨ p5)) → (((((p2 → (True ∨ p1)) → p5) → True) → p1) ∨ p2))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_22924667209523496603834170530 : (((p1 ∧ ((False ∧ p4) ∧ (p4 ∨ False))) ∨ ((((True ∧ ((False ∧ False) → True)) ∧ False) → ((((False ∧ p2) → True) ∧ False) → p5)) ∨ p3)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148642306833317818024080912130 : (((((False → p4) → (p3 ∧ (False → p3))) ∨ p5) ∧ (p5 → (((False → p1) → (p3 ∨ (p4 ∨ p1))) ∨ p2))) ∨ (True ∨ ((p2 ∨ p5) ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192130133978578943857168278076 : ((p5 → ((p5 → ((p3 ∧ False) → True)) → (p2 ∧ p2))) ∨ ((p5 ∨ p2) ∨ ((p1 → p4) ∨ ((False ∨ False) → ((p2 ∨ (False ∧ True)) ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41838118837481401074416223055 : ((((True ∨ (p1 ∨ p4)) ∧ ((p5 ∨ (((((True → p4) → ((False ∧ (False ∧ p5)) → (p4 → True))) ∧ True) ∨ False) → p3)) ∨ True)) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_792813840437280851833902960065 : (((True → ((p5 → (False ∨ p1)) ∧ ((p3 → (p1 ∨ p5)) → (p3 ∧ ((p2 ∨ p2) ∧ (p2 → (p3 → (p1 → ((p3 ∧ p5) ∨ p2))))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



