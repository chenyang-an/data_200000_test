variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747740399327426399402775812713 : ((((False → False) → (p3 ∧ (False ∧ (True → (p1 ∨ ((((p2 ∧ (p4 ∨ (((True → p1) ∨ False) → p2))) ∨ p2) ∨ p5) ∨ (p5 → p3))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112464056579983180577816857664 : (((((p3 → ((p3 → (False → p1)) → (p4 ∨ (p1 → False)))) ∨ ((p1 → False) → (((False ∨ p3) ∧ p1) → p3))) ∨ False) → p5) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66050344646061623618197420717 : ((p5 ∨ (((((p3 → True) ∧ (p4 ∧ ((False ∧ p2) ∨ (p1 ∧ (p4 ∧ ((((p1 ∧ True) → p4) ∨ p4) → p2)))))) → p3) ∨ p4) ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55332781528144894351860915416 : (((p4 ∨ (p1 → (p4 ∨ (p3 ∧ p5)))) ∨ (((((False ∧ p2) ∨ p5) ∨ (p4 ∨ p4)) → ((p4 → p3) → p1)) → (p4 ∧ (p3 ∨ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1787584923104878893536755773 : (((((p1 ∧ p5) ∧ (p5 → p2)) ∧ ((p1 → (p1 → p5)) ∧ False)) ∨ (((True → p2) → p1) → (p3 ∧ p5))) ∨ ((False → p4) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218981133622479396569420097761 : ((p4 ∧ ((p3 ∨ p2) → p5)) → (p5 ∨ (p2 → ((((p5 ∧ (((p3 ∧ True) ∨ False) ∧ (True ∨ p2))) ∧ p3) ∨ True) ∨ ((p3 → p5) ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66377626328355022663797749242 : ((p5 ∨ (p3 ∨ (((((p5 ∧ (p4 → True)) ∧ ((p4 → p5) ∧ p5)) ∧ p4) ∨ (p4 → (False → p4))) ∨ ((p2 → (p2 ∧ p4)) → p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136878052938070208208792454582 : (((p1 ∨ p2) ∨ ((p5 → (((p1 ∨ p3) → True) → ((False ∨ (((p2 ∧ (p4 ∧ True)) → False) ∧ False)) ∧ True))) ∧ p4)) ∨ ((p1 → p1) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_706051083770985244435162651163 : (((((p1 ∧ False) ∨ (True ∧ ((p4 ∨ p4) ∧ p5))) ∧ (p1 → ((p3 ∨ False) ∧ ((p3 ∧ (p4 ∧ (True ∧ (p2 ∧ (True ∨ p3))))) → p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694023117170143714886139462171 : (((((p1 ∧ ((p1 ∧ (p5 ∧ (True ∧ p2))) → (p2 → p3))) → (p4 ∧ p2)) ∨ (((p2 ∨ (p1 ∧ p5)) ∨ (p3 ∧ p2)) → (p2 ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117064494155647037500678416362 : (((p5 ∨ p4) → (p1 → ((((((p4 → True) ∧ p4) → p2) ∧ ((False ∨ p4) → p5)) ∨ p3) ∧ (p5 ∨ ((p2 ∨ True) ∧ p2))))) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168099116462715504985247865561 : ((((False ∨ p3) ∧ (p5 ∨ p4)) ∨ ((False ∧ ((p1 → (p4 ∨ p5)) ∧ p3)) ∨ (p3 ∨ True))) → ((((p4 ∨ p3) ∧ p5) ∨ False) ∨ (True ∨ p3))) := by
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
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- False on the left can always be used.
      apply False.elim h11
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215983383848683125805581654679 : ((p4 ∨ (p2 ∧ (p3 → p3))) ∨ ((p3 ∧ ((((True ∧ p2) ∧ ((p3 → (False → True)) ∧ p2)) ∧ True) ∨ (False ∧ (p1 ∨ p4)))) ∨ (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4162962822552587578137563547 : (p4 ∨ ((((p3 ∨ p5) ∨ ((((((True ∨ p4) ∨ p2) ∧ (p3 → p5)) ∧ False) → p3) → False)) ∧ True) ∨ ((p1 ∧ (p5 ∧ p2)) → p1))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354794598991515367200711592260 : (p5 → ((((True ∨ p3) → (p1 ∨ (True → p3))) ∨ ((False ∧ p3) ∨ (False ∨ ((True → ((((True ∧ p2) ∨ p5) ∧ p3) → True)) ∨ False)))) ∨ p2)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214805959377623711454439433538 : (((p2 ∨ p4) ∨ (False ∧ p1)) ∨ ((p4 ∨ (p1 → p1)) ∨ ((((True ∨ (p2 → (p5 → p1))) ∨ p2) ∨ True) ∨ (p1 ∨ ((p5 ∨ p4) → p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111004544539283532915845925363 : ((((p2 → ((((False ∨ (p4 ∧ (p3 ∨ p5))) ∨ (p5 → p5)) ∨ False) ∨ ((p2 → True) ∨ True))) ∧ (p1 ∧ (p3 → True))) ∧ False) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39365034705022759915553492037 : (((p3 ∧ ((((((True ∧ False) ∧ ((p4 → p1) ∧ True)) ∨ False) ∨ (p1 → p2)) ∨ (False ∨ (p2 ∧ (True ∨ p5)))) ∨ (p5 → True))) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134759920410033318496832366059 : ((((True ∨ p3) → ((p3 → p5) ∧ ((((p3 → True) ∧ ((p4 → p3) → p5)) ∨ p2) ∨ ((p2 → False) → False)))) → p1) ∨ (True ∨ (p5 ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41242960584607279029319891487 : ((((((((p5 → p1) ∧ ((p1 ∨ (p5 ∨ False)) → p1)) → p3) → (False ∧ (p3 ∨ True))) ∧ False) ∨ ((p2 ∧ (p3 ∨ p3)) → False)) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_775625335385140444159939777395 : (((False ∨ (False ∨ (p5 ∧ ((False ∨ p5) ∨ (((p4 → ((False ∧ (((p3 → p4) ∧ p1) ∨ (p5 ∧ p1))) ∧ p1)) ∧ p5) ∧ (True ∧ p4)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51266809185701941666684581400 : ((((p3 ∨ True) → (((((True ∧ (p2 → False)) ∧ True) ∧ (p2 ∨ (True ∨ p5))) → False) ∨ True)) ∨ (True → (False → ((p5 ∨ p3) ∨ True)))) ∨ p3) := by
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
theorem thm_5_vars_233708292831157733408851574507 : ((p2 ∨ (p5 → p5)) → (((((((p1 → p5) ∨ p4) → p4) ∨ p3) → p1) ∨ (p3 ∨ (p1 → ((((p2 ∧ p3) ∧ p4) ∨ p1) ∨ p1)))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58120944839195872782083610794 : (((p2 ∧ True) ∧ (((((p1 → (True ∨ True)) ∧ p5) ∧ (True ∨ (p4 ∧ p2))) → p2) ∨ (((False ∧ False) ∨ (True ∨ p5)) ∧ (p4 → p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118888811800564888794282513859 : ((True → (p3 ∧ (((p5 ∨ p3) ∧ True) → ((((p4 ∧ p4) ∧ (False ∨ ((p3 → (p2 ∧ p2)) → True))) → (p1 → p2)) → p1)))) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301148011002533262369128489073 : (False ∨ ((((p3 ∨ p3) → (p1 ∨ p5)) → (False ∨ p5)) ∨ ((((True ∨ (p2 ∧ True)) ∧ False) → ((True ∨ p1) ∧ False)) ∨ ((p1 → p1) ∨ p1)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192248405632586887229428843479 : ((((True ∨ (p2 ∧ (False ∨ p1))) → (True ∧ False)) ∧ p4) → (((p1 ∨ ((p4 → p4) → p2)) ∨ ((p2 ∨ (p2 ∧ (p2 ∨ False))) ∨ p2)) ∧ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (True ∨ (p2 ∧ (False ∨ p1))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h9 : (True ∨ (p2 ∧ (False ∨ p1))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h10 := h7 h9
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197783866117222596243488450822 : (((p5 → (False ∨ p3)) ∧ (p3 ∨ (p2 → False))) ∨ (p5 ∨ (((((p4 → (p4 ∨ (False ∧ p4))) → p4) ∨ (True → (p2 ∧ False))) ∧ False) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_602129441647595815471473268719 : ((((p5 ∧ ((True ∨ (True → (p3 ∨ (p1 → (p2 → p5))))) → ((p1 ∨ (p3 ∧ (False ∨ p1))) ∧ (p4 → (p3 ∧ (p1 ∨ True)))))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348197816555749510200332067212 : (p3 → ((True → p2) → ((False ∨ p1) → ((((p4 → p3) → (((p1 → p1) → p5) → False)) ∨ p1) ∨ (((False ∧ (p5 ∨ p1)) ∨ p5) ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2641721087910261749793262981 : (((((False ∧ p5) ∧ p2) ∧ p5) ∧ False) ∨ (((True ∧ p1) ∨ ((True → (p5 → p2)) ∨ ((p3 ∧ False) → ((True → p1) ∨ p4)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_586500611824937711410588386181 : (((((((p1 → p3) ∨ p2) → ((False ∧ (p2 ∨ ((p3 ∧ p1) ∧ (((((p5 → p5) ∨ p1) ∨ p4) ∧ False) ∨ p4)))) ∧ p5)) ∧ p3) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216963472817212349484526414711 : (((p2 → (p2 ∨ True)) ∧ p4) → (p5 ∨ ((True → True) ∧ ((p5 → False) ∨ (True ∧ ((((p2 ∧ p2) ∧ (p1 ∨ p1)) ∧ (p2 ∨ p1)) → True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232338164975896964508434169308 : (((p4 → False) → False) → ((((p3 → p3) ∧ (p2 ∧ p2)) ∧ (p2 → False)) ∨ (p1 → (((p4 → ((p3 ∨ p1) ∨ (p4 ∨ p5))) ∨ False) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624823843242142468304790463550 : ((((p5 ∨ ((p1 ∧ ((p1 ∨ p2) → (p2 → ((False → p2) → (((p4 ∧ p2) ∨ (p3 ∧ p4)) ∧ (False ∧ p2)))))) ∧ (p4 → True))) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158571411403428231090870512450 : ((True ∧ (((p3 → p4) → (p1 ∧ ((p3 → p1) → p5))) ∧ ((p2 ∨ ((p3 ∨ False) ∧ p3)) ∨ True))) ∨ (((p3 → True) ∧ True) ∨ (p4 ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262318785862205742489066463888 : (True ∧ (((((False → (False ∧ p1)) ∧ (True → False)) ∨ True) ∧ ((True → ((p1 ∨ p4) → p4)) → (p3 ∧ (((p1 → True) ∨ p3) ∧ False)))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49648763360052382037947910776 : (((((p5 ∧ p4) ∧ (False ∧ p2)) → ((False → (p1 ∨ ((p2 ∨ ((p3 ∨ p4) → True)) ∨ (p4 → True)))) ∨ False)) → (False ∨ (p3 → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137836838146360656021884719278 : ((p3 ∨ ((True → (((p4 ∨ (((False → p1) ∨ (True ∧ False)) ∨ p2)) ∨ p1) → p5)) ∨ (False ∧ (p3 ∨ (p4 ∧ p3))))) ∨ (False → (p3 ∧ p3))) := by
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
theorem thm_5_vars_306390506110141656582579074149 : (p1 ∨ ((p5 → p5) ∧ (p3 ∨ (((p2 ∧ p5) ∧ p4) ∨ (p1 ∨ ((p5 → p2) ∨ (True ∧ (True ∨ (True ∨ ((p4 ∨ (p5 ∨ True)) ∨ p1)))))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_615769503212807685287206337775 : (((((p2 → (((p1 → ((p4 ∨ True) ∨ p3)) → p3) ∨ (p5 ∧ (p2 ∨ p5)))) ∧ (((p2 → (p5 ∧ p2)) → p2) ∨ (p3 ∧ p2))) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_66222284328849987297627909598 : ((p5 ∨ (((((False ∨ p4) → (p5 ∨ (True ∨ False))) ∧ p1) ∨ p5) ∨ (False ∧ ((False → p2) ∧ ((p3 ∧ p4) ∧ ((p3 ∧ p1) ∨ p2)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215247620746747563599758998023 : ((False ∧ ((p1 → p4) → False)) ∨ ((((True → p3) ∨ ((p1 ∨ False) ∨ ((True ∨ True) ∨ (p2 ∨ p4)))) ∨ (((p4 ∨ True) ∨ p4) → p2)) ∨ p4)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227752012534172028772882225760 : ((p1 ∧ (p3 ∨ p3)) ∨ ((True ∨ (((p3 ∨ ((False ∨ True) ∨ p5)) ∧ (p1 → p4)) → ((p5 ∨ (p1 ∨ p5)) ∨ p2))) → (p1 ∨ (False → False)))) := by
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
theorem thm_5_vars_322791309377487328308099894010 : (p5 ∨ (((((((False ∧ (p2 ∨ (p1 ∧ True))) ∨ (p3 ∧ (True ∨ p4))) ∧ (p2 ∨ p3)) ∧ p4) ∧ p1) ∧ ((p1 → p5) ∧ (p2 ∨ p1))) → p5)) := by
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
  cases h8
  case inl h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- False on the left can always be used.
    apply False.elim h11
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h3.left
        let h19 := h3.right
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h20 =>
          -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
          have h21 : p1 := by
            -- One of the premise coincides with the conclusion.
            exact h5
          -- We have shown the premise of h18, we can now drive its conclusion.
          let h22 := h18 h21
          -- One of the premise coincides with the conclusion.
          exact h22
        case inr h23 =>
          -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
          have h24 : p1 := by
            -- One of the premise coincides with the conclusion.
            exact h23
          -- We have shown the premise of h18, we can now drive its conclusion.
          let h25 := h18 h24
          -- One of the premise coincides with the conclusion.
          exact h25
      case inr h26 =>
        -- Conjunctions on the left can always be decomposed.
        let h27 := h3.left
        let h28 := h3.right
        -- Disjunctions on the left can always be decomposed.
        cases h28
        case inl h29 =>
          -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
          have h30 : p1 := by
            -- One of the premise coincides with the conclusion.
            exact h5
          -- We have shown the premise of h27, we can now drive its conclusion.
          let h31 := h27 h30
          -- One of the premise coincides with the conclusion.
          exact h31
        case inr h32 =>
          -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
          have h33 : p1 := by
            -- One of the premise coincides with the conclusion.
            exact h32
          -- We have shown the premise of h27, we can now drive its conclusion.
          let h34 := h27 h33
          -- One of the premise coincides with the conclusion.
          exact h34
    case inr h35 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h36 =>
        -- Conjunctions on the left can always be decomposed.
        let h37 := h3.left
        let h38 := h3.right
        -- Disjunctions on the left can always be decomposed.
        cases h38
        case inl h39 =>
          -- We want to use the implication h37 based on <expert-advice>. So we show its premise.
          have h40 : p1 := by
            -- One of the premise coincides with the conclusion.
            exact h5
          -- We have shown the premise of h37, we can now drive its conclusion.
          let h41 := h37 h40
          -- One of the premise coincides with the conclusion.
          exact h41
        case inr h42 =>
          -- We want to use the implication h37 based on <expert-advice>. So we show its premise.
          have h43 : p1 := by
            -- One of the premise coincides with the conclusion.
            exact h42
          -- We have shown the premise of h37, we can now drive its conclusion.
          let h44 := h37 h43
          -- One of the premise coincides with the conclusion.
          exact h44
      case inr h45 =>
        -- Conjunctions on the left can always be decomposed.
        let h46 := h3.left
        let h47 := h3.right
        -- Disjunctions on the left can always be decomposed.
        cases h47
        case inl h48 =>
          -- We want to use the implication h46 based on <expert-advice>. So we show its premise.
          have h49 : p1 := by
            -- One of the premise coincides with the conclusion.
            exact h5
          -- We have shown the premise of h46, we can now drive its conclusion.
          let h50 := h46 h49
          -- One of the premise coincides with the conclusion.
          exact h50
        case inr h51 =>
          -- We want to use the implication h46 based on <expert-advice>. So we show its premise.
          have h52 : p1 := by
            -- One of the premise coincides with the conclusion.
            exact h51
          -- We have shown the premise of h46, we can now drive its conclusion.
          let h53 := h46 h52
          -- One of the premise coincides with the conclusion.
          exact h53



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671211353669104110649920379134 : ((((p3 ∨ (p1 ∧ (((p5 ∧ p1) ∨ ((p1 → (p4 ∨ p2)) ∨ ((False ∨ False) → (True → p1)))) ∨ (p5 ∨ p3)))) ∨ (p5 ∨ (False → False))) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_165134583030191394394063633956 : ((((p3 ∨ (((p5 ∨ (True ∧ (p4 ∧ True))) ∧ (p5 ∨ p4)) ∧ p3)) ∨ True) ∧ (True ∨ p1)) ∨ (p1 ∨ (p1 → (False → ((p2 → p2) ∨ p2))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_8206331004892093788507475403 : ((((p4 → ((p2 ∨ (p1 ∨ p2)) ∨ (((False → p2) → (p3 ∨ ((True → True) → (p5 → (p1 ∨ (False → p3)))))) ∧ True))) ∨ p4) ∨ False) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208600853463298170246441883611 : (((p3 → p4) → ((False ∧ True) → p4)) → (((((p1 ∨ (((p5 → False) → (p1 → p3)) ∧ (p2 ∨ p2))) ∨ True) ∨ (p5 ∨ p5)) → False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_781718327533608414724517595517 : (((p2 ∨ (p4 ∨ ((p1 → ((p4 ∧ ((False ∨ p1) ∨ p3)) ∨ ((((p4 ∧ p2) ∧ (False ∨ p2)) ∧ False) ∨ False))) → (p2 ∧ (p2 ∨ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56997133226364730308793441229 : (((p5 ∨ (p5 → p4)) ∧ ((p5 ∧ (((p4 ∨ p3) ∧ p2) ∨ (True → ((True ∧ False) → (p4 → (p5 → p4)))))) ∨ ((p4 → p2) ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679131945632905850620741469270 : ((((p3 ∨ (((p4 → p4) → (True → ((((p4 → p5) → p2) → (p3 ∨ p3)) ∧ p2))) ∧ (p3 ∨ p3))) ∨ (False → ((p4 ∧ False) → False))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59337941469915590104674037865 : (((p4 ∨ p5) ∨ (p5 ∨ (((p3 ∧ p3) ∨ p1) ∨ ((((p4 ∨ ((p3 ∧ (p1 ∧ True)) → (p3 ∨ False))) ∨ True) ∧ (p4 → p1)) → True)))) ∨ p3) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181063062905301425392288278453 : (((p5 ∧ p4) → ((p3 ∧ ((False → (p2 ∧ p2)) → p4)) ∧ (p3 ∨ p1))) → ((((False ∨ (True ∧ p2)) → (p3 ∧ p5)) ∨ (False → p1)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256446373741211163753128083409 : ((False ∨ p3) → (p2 → (p4 ∨ ((p1 ∨ (p4 ∨ ((((p5 → p1) ∧ p4) → (((p3 → p1) ∨ p2) ∨ p5)) ∧ p3))) ∨ (True ∨ (p4 ∨ False)))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171762768327336063581517797267 : (((((p4 ∨ (((True → p2) ∨ (p3 → p1)) ∨ p2)) → (False ∨ p4)) → p1) → False) ∨ (p3 ∨ ((False ∨ (True ∧ False)) → (p2 ∧ (p4 ∨ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h5
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618627232548786277835209662282 : ((((((False ∧ p2) ∧ p5) ∧ ((p4 ∨ (p3 ∧ ((p3 ∧ True) ∨ p3))) ∧ ((((True ∨ (False ∨ p3)) ∧ False) → (p4 → p2)) → p4))) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39273599237372974468071169624 : (((False ∧ (p5 → ((p2 ∧ (False → p3)) ∨ ((p1 → False) ∧ (p3 ∧ (((((p2 ∧ (p4 ∨ p1)) → False) ∨ p2) → True) ∧ p2)))))) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_692890434517044503430426966433 : (((((p2 ∧ p4) ∧ ((((True → p4) ∨ p2) → (p3 ∨ p1)) → (p2 → p3))) ∧ ((p4 ∧ (p1 ∧ p2)) → ((p3 → (p2 → p5)) ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231751840367165494081742567075 : (((p3 ∧ False) → p5) → (((False → p2) ∨ p4) → ((((p1 → (p4 → True)) ∧ ((False ∧ p2) ∨ p3)) ∨ True) ∨ ((True ∨ False) → (False ∧ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_878428892701665573406945850246 : (((((False → False) → (((((p2 → p4) → (False ∧ (p4 ∨ (p4 ∧ True)))) ∨ p1) → ((p1 ∧ p4) → True)) ∧ (p2 ∧ p5))) ∧ (p5 → False)) → False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : p5 := by
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : (False → False) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h6
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h5
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h10 := h3 h4
  -- False on the left can always be used.
  apply False.elim h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181511503101520513198241652877 : ((p5 ∨ (p4 ∨ ((True ∧ ((False → p3) ∨ ((False ∧ p1) ∧ p1))) ∧ p5))) → ((((p2 ∨ p1) ∨ (p4 ∨ ((False ∨ p4) ∧ p4))) ∧ p2) ∨ True)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- Conjunctions on the left can always be decomposed.
        let h14 := h12.left
        let h15 := h12.right
        -- False on the left can always be used.
        apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134707804293811092468660536954 : ((((p2 ∨ (p5 → (p3 ∧ p2))) → ((p1 ∨ (p1 ∨ (p2 → p1))) ∧ (((p3 → False) → p1) ∨ (p5 ∧ p1)))) → p1) ∨ (False → (False ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340725496420705272263812238485 : (p2 → (((p1 → (((p1 ∨ p2) ∨ (p2 ∨ (False ∧ (((p2 ∧ (p5 ∨ p3)) ∨ p3) → p2)))) ∧ ((True ∨ p1) → (False ∨ p3)))) ∧ p5) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_913793671142192923363573217940 : ((((((((p4 → ((p2 → (p2 → p5)) ∧ False)) ∨ p2) ∧ p5) ∧ (False → True)) ∧ p2) ∧ ((p4 ∨ (p2 ∨ p5)) ∧ ((p3 ∧ p2) ∨ p3))) → p5) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h3.left
    let h12 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h17 =>
        -- One of the premise coincides with the conclusion.
        exact h9
    case inr h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h20 =>
          -- Conjunctions on the left can always be decomposed.
          let h21 := h20.left
          let h22 := h20.right
          -- One of the premise coincides with the conclusion.
          exact h9
        case inr h23 =>
          -- One of the premise coincides with the conclusion.
          exact h9
      case inr h24 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h25 =>
          -- Conjunctions on the left can always be decomposed.
          let h26 := h25.left
          let h27 := h25.right
          -- One of the premise coincides with the conclusion.
          exact h24
        case inr h28 =>
          -- One of the premise coincides with the conclusion.
          exact h24
  case inr h29 =>
    -- Conjunctions on the left can always be decomposed.
    let h30 := h3.left
    let h31 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h30
    case inl h32 =>
      -- Disjunctions on the left can always be decomposed.
      cases h31
      case inl h33 =>
        -- Conjunctions on the left can always be decomposed.
        let h34 := h33.left
        let h35 := h33.right
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h36 =>
        -- One of the premise coincides with the conclusion.
        exact h9
    case inr h37 =>
      -- Disjunctions on the left can always be decomposed.
      cases h37
      case inl h38 =>
        -- Disjunctions on the left can always be decomposed.
        cases h31
        case inl h39 =>
          -- Conjunctions on the left can always be decomposed.
          let h40 := h39.left
          let h41 := h39.right
          -- One of the premise coincides with the conclusion.
          exact h9
        case inr h42 =>
          -- One of the premise coincides with the conclusion.
          exact h9
      case inr h43 =>
        -- Disjunctions on the left can always be decomposed.
        cases h31
        case inl h44 =>
          -- Conjunctions on the left can always be decomposed.
          let h45 := h44.left
          let h46 := h44.right
          -- One of the premise coincides with the conclusion.
          exact h43
        case inr h47 =>
          -- One of the premise coincides with the conclusion.
          exact h43
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46821090891225230930031870533 : (((((False → (p4 → (False ∨ (((p3 → (p1 ∧ True)) ∧ (((p1 → p1) → p2) → False)) ∧ (p5 ∨ False))))) → p3) ∧ False) ∨ (True ∨ False)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_103128802139859915799143765260 : ((((p2 ∧ p4) ∧ (((False → (p2 ∨ p2)) ∧ ((((p2 ∨ p1) ∧ ((p5 → p4) ∨ (p1 → False))) ∨ True) ∧ p2)) ∨ p4)) ∨ True) ∧ (True ∨ True)) := by
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
theorem thm_5_vars_305419374597744602151740185978 : (p1 ∨ ((p2 ∨ ((p3 ∨ (((p4 ∧ (p5 ∨ True)) → p3) ∨ (p3 → True))) ∧ (p4 → p4))) ∨ ((((p3 ∧ (p1 → True)) ∧ p4) → False) → p1))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_98816326852503455547529061991 : ((True → ((((p3 ∨ True) ∧ p4) ∧ (p2 ∨ (((True → p2) ∧ p4) ∨ (p5 → (p2 ∨ (p4 ∨ (p4 ∨ (p1 ∧ (p1 ∨ p5))))))))) ∧ False)) → False) := by
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179316152977052914083757309045 : ((False ∨ (False ∨ (p5 → (((p1 ∨ False) ∨ (p2 ∧ (p3 ∨ True))) ∧ p2)))) ∨ ((((False → (p1 ∨ (p4 ∨ (p4 ∧ p3)))) ∨ p1) → True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654577821010012425386135279025 : (((((p4 ∨ (((True ∨ p1) → (p4 ∧ (True → (((True → (p1 ∧ p2)) ∧ p4) ∨ (p1 ∧ (p2 ∧ p2)))))) ∨ p5)) ∨ True) ∨ (p3 ∧ p1)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_564540978278879593882136057 : (((p4 → ((((((p4 ∧ p4) → p4) ∨ (False ∨ (False ∨ (True ∨ p5)))) ∨ p3) ∧ p5) ∧ (p3 ∨ (p1 ∨ (False ∧ p2))))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_763587302776748862020824995962 : (((p3 ∧ (p4 ∧ (((False ∨ ((((False → p4) ∧ (p3 ∧ (p4 ∨ p3))) ∨ (p3 ∧ p1)) ∧ p3)) ∧ (True → p5)) ∨ (False ∧ (p2 ∨ p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342770091684308650948628893088 : (p2 → ((p5 ∨ (p5 ∨ ((p5 ∧ p2) ∧ (False ∨ p3)))) ∨ (p1 → (True ∨ ((p1 ∨ (((p2 ∨ (p2 → p5)) ∧ p5) ∨ p5)) → (True ∨ True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234048399808505824322758155220 : ((p5 ∨ (p3 → p1)) → ((p4 ∨ (p4 ∨ ((False ∧ p4) ∨ (p3 ∨ p2)))) ∨ (((p4 ∨ p2) → (p5 → False)) ∨ (p3 ∨ (True ∨ (p4 ∨ True)))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
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
theorem thm_5_vars_55057087278725718908935979472 : (((p1 ∨ (False ∨ ((p3 ∨ p3) → True))) ∧ ((((((False ∨ p4) ∧ (((p3 → (p4 ∧ False)) ∧ p3) → True)) ∧ p3) ∧ True) ∧ p5) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50893094191661347929966559358 : ((((p4 ∧ ((p1 ∧ (p2 → p3)) → (True ∧ (p3 ∨ (p5 ∨ ((p1 ∨ True) ∧ p2)))))) → p3) ∧ (False ∨ (((p1 ∨ p3) ∨ p2) ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148052417573631809419276863595 : (((False ∨ (((((p3 ∧ (p1 → ((p1 ∨ p2) → False))) ∨ True) ∨ (p5 ∨ False)) → False) → p3)) ∨ (True ∨ p5)) ∨ ((p1 → (p1 ∧ p4)) ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264619784609554738493395052420 : (True ∧ (((p3 → p3) ∨ p3) → (((p5 ∨ p5) ∧ (True ∧ ((p3 ∨ p2) ∨ True))) ∨ ((((p2 ∨ p1) → p1) ∧ False) → (p2 ∧ (p1 ∨ p3)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h3.left
    let h7 := h3.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- False on the left can always be used.
    apply False.elim h11
    -- Conjunctions on the left can always be decomposed.
    let h12 := h9.left
    let h13 := h9.right
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161863342777612492011518115607 : ((False → (((False ∨ ((True ∨ p4) ∧ (p3 → p3))) ∧ ((p5 ∧ p1) ∧ (False → (False ∨ True)))) ∧ p4)) → (((p1 → p3) ∨ p2) ∨ (p3 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_8277397674322829966783006354 : ((((((p1 → ((p5 → True) ∧ True)) ∧ (((False → p2) ∨ (((p1 → p2) ∧ p3) ∧ (False → False))) → (p1 ∨ p1))) → False) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137863288427647894102198208681 : ((p3 ∨ (False ∨ ((((p1 ∨ (False ∧ p1)) → False) ∧ (p1 ∧ True)) → (((True ∨ p3) ∨ (p2 ∧ p3)) → (p2 ∨ False))))) ∨ ((False ∨ False) ∨ False)) := by
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
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h9 : (p1 ∨ (False ∧ p1)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h10 := h5 h9
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h1.left
      let h13 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
      have h16 : (p1 ∨ (False ∧ p1)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h14
      -- We have shown the premise of h12, we can now drive its conclusion.
      let h17 := h12 h16
      -- False on the left can always be used.
      apply False.elim h17
  case inr h18 =>
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- Conjunctions on the left can always be decomposed.
    let h21 := h1.left
    let h22 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h23 := h22.left
    let h24 := h22.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47009256542376833344957175158 : (((((p4 → False) → (False ∨ (p5 ∨ (p5 ∨ ((((p5 ∨ p5) ∧ False) ∨ (False ∨ p1)) ∧ ((p4 → p3) ∧ p3)))))) → p4) ∨ (p4 → p4)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358085660249981700052054630240 : (p5 → (p1 ∨ (p3 → ((p4 ∧ (p2 → (p2 → p4))) → (((p2 ∨ ((True ∧ p1) ∧ False)) ∧ False) ∨ (p1 → (((False → p3) ∨ True) → p4))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_195000651677717915650371677773 : (((p3 ∧ (((True ∧ p4) ∧ p2) → p4)) → p3) ∧ (((p2 ∧ (((p2 ∧ True) ∨ (p3 ∧ p1)) ∨ True)) ∨ p3) ∨ (p3 ∨ (True → (p4 ∨ True))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117678498254115246372974757202 : ((p3 ∧ ((((True ∨ p5) → p3) → (False → (p3 → True))) → (((((True → ((True ∨ False) ∨ p1)) → p4) → True) → p1) ∧ p3))) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53606061586408323303281514257 : ((((p4 ∧ (False ∧ ((p2 → p2) → p5))) ∧ (False ∧ p2)) ∧ (((((False ∧ p1) ∨ (p2 ∨ p2)) ∧ True) → p2) → (p1 ∨ (True ∨ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201121663346527261652177615164 : ((True → (True ∨ (p4 ∧ ((p3 ∧ p2) ∨ p4)))) → ((((p2 ∧ (p4 ∨ p2)) ∨ False) ∨ (p4 ∧ (((p5 → (p1 ∧ p2)) → p5) → False))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_741538986733481244640770104548 : ((((p5 ∨ p4) ∨ ((((((p4 → p1) ∨ (p3 ∧ p5)) ∨ True) → p5) ∨ ((((p4 ∨ p4) → (p2 ∨ p2)) ∨ (p5 → p3)) → False)) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_176964809209335728243964387317 : (((p4 ∧ p4) → (p3 → ((p4 → (True ∧ (p4 ∧ p4))) ∨ (p3 ∧ False)))) ∧ ((p1 → (True ∧ ((p3 → p5) → ((True → False) ∨ False)))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h5
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_95431113456889146521918692657 : ((p5 ∧ ((p5 → (((p2 ∨ True) ∧ p5) ∧ ((False → (p5 ∧ (((p1 ∨ p5) → ((p1 ∧ p4) ∨ p3)) ∧ (p4 ∨ p4)))) ∧ p3))) ∧ p1)) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349996232630124433887182599909 : (p4 → ((((((p4 ∧ p2) → p4) ∨ p3) ∧ (((((False → True) ∧ p5) ∧ ((p5 → True) → p3)) ∧ (p4 ∨ (p2 ∧ p1))) ∧ p4)) ∨ p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308437184523309034072347045095 : (p2 ∨ (((p4 ∧ ((((p3 ∨ (p4 ∨ p2)) → p2) ∨ p3) → (p5 ∧ (((p3 ∧ (p4 ∨ (False ∧ (p2 ∧ p3)))) → p2) ∨ p4)))) → p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54054419659590433507670547203 : ((((((True → p2) ∨ True) ∨ p1) → (p4 ∨ (False ∧ p5))) → ((True → True) → (((True ∧ p4) ∨ (((p3 ∨ p3) → p5) → p3)) → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38475492212283735335267044525 : ((((((p2 ∧ ((p2 → ((p2 ∧ p4) → p3)) → p3)) ∨ p5) → False) ∧ (((p2 ∧ ((p1 → True) ∨ (p2 ∨ p1))) → p5) ∧ False)) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168756658789327382320011877295 : ((False ∨ (p4 ∨ (((p2 → (p1 → p1)) → True) ∨ (((True ∨ p5) ∧ p4) ∧ (p4 → False))))) → ((p2 ∨ p2) ∨ (True → (p1 → (p1 ∧ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h6
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h9
        -- Implications on the right can always be decomposed.
        intro h10
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h10
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
        cases h14
        case inl h16 =>
          -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
          have h17 : p4 := by
            -- One of the premise coincides with the conclusion.
            exact h15
          -- We have shown the premise of h13, we can now drive its conclusion.
          let h18 := h13 h17
          -- False on the left can always be used.
          apply False.elim h18
        case inr h19 =>
          -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
          have h20 : p4 := by
            -- One of the premise coincides with the conclusion.
            exact h15
          -- We have shown the premise of h13, we can now drive its conclusion.
          let h21 := h13 h20
          -- False on the left can always be used.
          apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178406533804012050400153671565 : ((((False ∨ False) → ((p5 ∨ (p3 ∧ p4)) ∧ (p2 → True))) → (p4 ∧ p2)) ∨ (((p1 → False) → p4) → (p1 ∨ (((p3 ∧ p2) → p2) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185020142832851253833292736015 : (((p3 ∨ True) ∧ ((((False ∧ p4) → p1) → (p2 → p4)) ∨ p2)) ∨ (True ∨ (p4 ∨ ((p4 ∧ (False → p3)) → (p4 ∧ (p5 ∧ (False ∧ p1))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178230088618062212982821041496 : (((p3 → (((p5 → (p1 ∧ p4)) → (p3 ∧ (p1 → False))) ∧ p3)) → False) ∨ (p3 ∨ (p5 → (True ∨ (p5 ∨ ((p3 ∧ p2) ∧ (p2 ∧ p3))))))) := by
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
theorem thm_5_vars_49470838693492783781417349958 : ((((((p2 ∧ (((p3 ∨ (((False ∧ (p3 → False)) ∨ p4) → True)) ∧ False) → (False → p4))) ∨ p1) ∨ p1) → p3) → ((False ∧ p5) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



