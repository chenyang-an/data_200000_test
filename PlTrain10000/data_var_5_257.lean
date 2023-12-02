variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40691945490117804903797898002 : ((((((p4 ∧ (p5 ∧ p3)) ∨ (((((False ∨ (p5 ∧ p5)) ∧ False) → True) → True) ∧ p2)) → (((p5 ∨ p5) ∧ True) ∨ p4)) → p4) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47820673573811037089288831992 : (((((((p4 ∨ False) → (p4 ∧ (p2 ∨ True))) ∧ p4) → ((((p5 ∨ (p4 → (p3 ∧ True))) → p2) → p5) ∧ True)) → p2) → (p1 → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148715259634989580492436530891 : ((((p4 → (p3 ∨ p2)) → ((p3 ∧ p2) → p4)) → (p4 ∨ (False ∨ (((p2 ∨ p3) ∨ p4) → (False ∨ False))))) ∨ ((p4 → True) → (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140163868043632185815611360169 : ((((p1 ∨ (((p2 ∧ (p3 ∧ (p3 → (p4 → (p2 → True))))) ∨ (p5 ∧ p3)) ∨ True)) ∨ (True ∨ True)) → (p2 ∧ p3)) → (p2 ∨ (p2 ∧ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p1 ∨ (((p2 ∧ (p3 ∧ (p3 → (p4 → (p2 → True))))) ∨ (p5 ∧ p3)) ∨ True)) ∨ (True ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134188087713046309671249553743 : ((((((((p4 → (p3 ∧ p2)) ∨ True) ∨ (p1 ∧ p5)) → p4) ∨ p5) → ((True → p3) → ((p1 → p4) ∨ False))) ∨ True) ∨ ((p2 → p1) → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54520087093725813382059213837 : ((((p2 ∨ p4) ∧ ((p1 ∧ (False → False)) → p5)) ∨ (False ∨ (p3 → ((((p3 ∨ p5) ∧ ((False ∧ (True → p5)) → True)) ∨ p5) → p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307487764969015195816783091854 : (p1 ∨ (True → ((True → ((p4 ∧ False) ∨ (((True ∧ p2) → (((p1 → p5) ∨ p4) ∨ ((False ∨ False) ∨ (p4 ∨ p4)))) ∨ (p4 ∨ p5)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619428685294685123875523903061 : (((((p4 ∧ (p1 → p4)) → (((((p5 → p2) ∨ True) → (False ∨ p1)) ∧ (False → ((((True ∨ p3) ∧ p4) ∨ p2) ∧ p1))) ∨ p5)) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_14991803667739614456164483297 : ((((False ∧ p4) ∨ ((False ∨ (((p5 ∨ (False ∧ p3)) ∧ ((((False → p2) ∨ p3) ∨ p4) → p2)) ∨ (True ∨ p4))) ∨ True)) ∨ (False → p3)) ∧ True) := by
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
theorem thm_5_vars_313371576047788184190738615521 : (p3 ∨ ((p5 → ((p2 ∧ (((p1 ∧ (((p5 ∨ ((p4 ∧ (p5 → p2)) ∧ True)) ∧ p1) → p5)) ∨ (False → p5)) → p1)) ∨ (False ∨ True))) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42895637279216854455418711056 : (((p3 → ((p4 ∨ (((p3 ∨ (p2 → ((p1 ∧ p1) → (p4 ∧ True)))) → (p1 ∨ p5)) ∨ p4)) ∧ (p5 → ((p1 ∨ True) ∨ p3)))) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63446668824269557819894798960 : ((p5 ∧ (p4 → ((p5 ∧ ((p5 ∧ ((((p4 ∧ p4) ∧ False) ∧ p5) → (p3 ∧ (p1 ∨ (p3 → p4))))) → p3)) ∨ ((p3 → p5) ∨ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340050281399662533826150199318 : (p1 → (p2 → (((p1 ∨ True) ∧ (((((p5 → p1) ∨ p1) → False) ∧ p5) ∨ False)) ∨ ((((p5 → False) ∨ False) ∧ (True ∧ (p2 ∨ p5))) → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45049799195816288502603997148 : ((((False → p3) ∨ (((p1 ∧ (True ∧ p3)) ∨ p1) → ((p3 ∨ ((True ∧ p1) → (False ∨ p4))) ∨ ((False ∧ (p5 ∧ p5)) ∧ False)))) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191108303983672053204038206547 : (((p2 ∧ (p1 ∨ p4)) ∧ (p4 ∧ ((p4 ∧ True) ∧ True))) ∨ ((True ∨ ((p4 → (p4 ∨ (p5 ∧ (p3 ∨ p1)))) ∧ ((True → True) ∧ p4))) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_728304899454528869806992328 : (((p1 → (False ∧ (p4 ∧ (False ∧ True)))) → ((((p2 ∨ (p4 ∧ p2)) ∨ False) ∨ (True ∨ ((True ∨ (p1 ∨ p1)) ∧ p4))) ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252435052028882059069964542993 : ((p5 → False) ∨ (p5 ∨ (p2 → (((((p5 ∧ ((p3 → (False ∨ (False ∨ p3))) ∧ p4)) ∧ ((p3 ∨ p3) ∨ True)) ∧ p5) ∨ (p1 ∨ p5)) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3150690992741262022897789476 : ((p2 → True) ∧ ((((p5 ∧ p5) ∨ (p5 ∨ (p4 ∨ ((((p3 ∧ p3) ∨ (True ∨ (p1 → (p5 ∨ p2)))) ∨ p5) → False)))) ∨ p2) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747296784184972837263896847651 : ((((p5 ∨ p3) → ((((p3 ∧ (False ∧ p2)) → (p4 ∧ p4)) ∨ p3) ∧ ((True ∧ (p2 → ((True ∧ (p4 → p2)) → (p2 ∧ p5)))) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137646098221595094207837468622 : ((False ∨ ((((p3 → (p4 → True)) → True) ∨ p4) → ((((p1 ∧ True) ∨ (p1 ∧ True)) ∨ False) ∨ (False → (p3 ∨ p2))))) ∨ ((True ∨ p5) → p4)) := by
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
theorem thm_5_vars_40497513392681445636836089876 : ((((True ∧ (((p1 ∨ p4) ∧ (((p3 ∨ True) ∨ p1) → p5)) → (((True ∧ p5) ∨ ((p1 ∧ (p2 → False)) ∨ p2)) → p3))) ∨ True) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_602717265561953346020929742008 : ((((False ∨ ((True ∧ p1) ∨ ((True ∧ (p5 ∧ (p1 → p5))) ∨ ((p3 ∧ (p1 ∧ (p2 → ((p2 ∧ p4) → (True ∧ p1))))) ∧ p3)))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42104914742267774950119963721 : ((((p2 ∧ True) → ((((p4 → p1) ∧ (False → (((p4 → True) ∨ p3) ∧ p4))) ∧ (p3 ∧ (p1 ∨ p4))) → ((p1 ∧ p1) ∧ p1))) ∨ p5) ∨ p2) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h4.left
  let h8 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h1.left
    let h11 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h1.left
    let h14 := h1.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h15 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h12
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h16 := h5 h15
    -- One of the premise coincides with the conclusion.
    exact h16
  -- Conjunctions on the left can always be decomposed.
  let h17 := h2.left
  let h18 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h19 := h17.left
  let h20 := h17.right
  -- Conjunctions on the left can always be decomposed.
  let h21 := h18.left
  let h22 := h18.right
  -- Disjunctions on the left can always be decomposed.
  cases h22
  case inl h23 =>
    -- Conjunctions on the left can always be decomposed.
    let h24 := h1.left
    let h25 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h23
  case inr h26 =>
    -- Conjunctions on the left can always be decomposed.
    let h27 := h1.left
    let h28 := h1.right
    -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
    have h29 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h26
    -- We have shown the premise of h19, we can now drive its conclusion.
    let h30 := h19 h29
    -- One of the premise coincides with the conclusion.
    exact h30
  -- Conjunctions on the left can always be decomposed.
  let h31 := h2.left
  let h32 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h33 := h31.left
  let h34 := h31.right
  -- Conjunctions on the left can always be decomposed.
  let h35 := h32.left
  let h36 := h32.right
  -- Disjunctions on the left can always be decomposed.
  cases h36
  case inl h37 =>
    -- Conjunctions on the left can always be decomposed.
    let h38 := h1.left
    let h39 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h37
  case inr h40 =>
    -- Conjunctions on the left can always be decomposed.
    let h41 := h1.left
    let h42 := h1.right
    -- We want to use the implication h33 based on <expert-advice>. So we show its premise.
    have h43 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h40
    -- We have shown the premise of h33, we can now drive its conclusion.
    let h44 := h33 h43
    -- One of the premise coincides with the conclusion.
    exact h44



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112157260520399274138467725948 : (((p2 ∧ ((p2 ∧ (p3 ∧ p2)) ∧ (p2 ∧ ((p1 ∨ (p4 → p2)) → ((False ∧ False) ∨ (((p1 → p5) ∨ p3) → p2)))))) ∨ True) ∨ (p2 → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_769836781526009014214486684784 : (((p5 ∧ (p4 ∨ (p2 → ((p5 ∧ (((p3 → ((p2 ∨ ((p2 → True) → p3)) ∨ (p4 ∧ p5))) → p3) → ((False ∨ p2) → False))) ∨ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_987145248716795329950296417686 : (((p2 ∧ (p4 ∧ (((((p2 ∧ False) ∨ p4) ∨ (p1 ∧ (p5 ∧ p1))) → False) ∧ ((p1 ∨ ((p1 ∧ p2) ∧ (p4 ∨ (p3 ∨ p5)))) ∨ p2)))) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h10 : (((p2 ∧ False) ∨ p4) ∨ (p1 ∧ (p5 ∧ p1))) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h11 := h6 h10
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Conjunctions on the left can always be decomposed.
      let h15 := h13.left
      let h16 := h13.right
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h17 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h18 : (((p2 ∧ False) ∨ p4) ∨ (p1 ∧ (p5 ∧ p1))) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h17
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h19 := h6 h18
        -- False on the left can always be used.
        apply False.elim h19
      case inr h20 =>
        -- Disjunctions on the left can always be decomposed.
        cases h20
        case inl h21 =>
          -- One of the premise coincides with the conclusion.
          exact h21
        case inr h22 =>
          -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
          have h23 : (((p2 ∧ False) ∨ p4) ∨ (p1 ∧ (p5 ∧ p1))) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h4
          -- We have shown the premise of h6, we can now drive its conclusion.
          let h24 := h6 h23
          -- False on the left can always be used.
          apply False.elim h24
  case inr h25 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h26 : (((p2 ∧ False) ∨ p4) ∨ (p1 ∧ (p5 ∧ p1))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h27 := h6 h26
    -- False on the left can always be used.
    apply False.elim h27
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342219814304148413190426078346 : (p2 → ((p1 ∧ (((p4 ∧ ((p5 ∧ p4) ∨ p3)) ∨ p2) → (False → (((True → p3) ∨ True) → (p2 ∧ p4))))) → (p5 ∨ ((p3 → p5) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114524314092507164326282303945 : (((p5 ∧ ((p5 → p2) ∨ (p3 → ((False ∧ (p3 ∨ ((p4 ∨ p5) ∨ (p3 → p1)))) → False)))) → (((p1 ∧ True) → False) ∧ p2)) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149564598928383549268141109840 : ((p2 ∧ ((True → p5) → ((((p5 ∨ p3) ∧ ((p3 → p2) ∧ p5)) → p1) ∧ ((p1 → p4) → (p2 → p5))))) ∨ (p1 → ((True ∨ p2) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208341216697108371785405065922 : (((p4 → True) ∧ (p2 ∧ (False → p2))) → (True → (p2 ∧ (((((p4 ∨ ((p5 ∨ (p3 ∧ False)) → p1)) ∨ True) ∧ True) ∨ p5) ∧ (p4 → p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h11
  -- Conjunctions on the left can always be decomposed.
  let h12 := h1.left
  let h13 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h13.left
  let h15 := h13.right
  -- One of the premise coincides with the conclusion.
  exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_107096728085172818963175718378 : (((p1 ∧ (p1 ∨ (p1 ∨ p4))) → (((p5 ∧ p1) ∨ False) ∨ ((p1 → p4) ∨ ((p2 → (p5 → (p2 ∨ (True → p4)))) ∨ p3)))) ∧ (p4 → p4)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h9
      -- Implications on the right can always be decomposed.
      intro h10
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h12
      -- One of the premise coincides with the conclusion.
      exact h11
  -- Implications on the right can always be decomposed.
  intro h13
  -- One of the premise coincides with the conclusion.
  exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245966113288708515060599602347 : ((p4 ∧ True) ∨ ((((p5 ∨ (((True → False) ∧ p1) ∧ ((((p1 ∧ (p1 ∧ True)) ∨ p4) ∧ p3) ∨ False))) ∨ p4) ∨ p4) → (p5 ∨ (p2 → True)))) := by
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
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h5 =>
        -- Conjunctions on the left can always be decomposed.
        let h6 := h5.left
        let h7 := h5.right
        -- Conjunctions on the left can always be decomposed.
        let h8 := h6.left
        let h9 := h6.right
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h10 =>
          -- Conjunctions on the left can always be decomposed.
          let h11 := h10.left
          let h12 := h10.right
          -- Disjunctions on the left can always be decomposed.
          cases h11
          case inl h13 =>
            -- Conjunctions on the left can always be decomposed.
            let h14 := h13.left
            let h15 := h13.right
            -- Conjunctions on the left can always be decomposed.
            let h16 := h15.left
            let h17 := h15.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h18
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h19 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h20
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h21 =>
          -- False on the left can always be used.
          apply False.elim h21
    case inr h22 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h23
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h24 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h25
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_595027535579027235827690701335 : ((((((p3 → ((p2 ∧ p1) ∨ p4)) ∧ ((((p4 → p3) ∨ p2) ∨ p5) ∨ True)) ∨ (p5 ∧ (((True → (p1 ∧ p5)) ∨ True) → p1))) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172393020478359105900073951224 : ((((p4 ∨ p1) ∧ (p4 → (p2 ∧ False))) → ((((p4 ∨ True) ∧ True) → p1) ∧ p2)) ∨ (True ∨ (((p5 → False) ∧ p1) → ((True ∧ True) → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42918743312551802398959764778 : (((p4 → (((((((((p5 → p4) ∨ (p4 → ((p2 ∨ p4) ∨ (False → p4)))) ∧ p2) ∧ p1) ∧ p5) ∨ p3) ∨ False) ∧ False) ∧ p2)) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_23078813834815484701151471884 : ((((((p2 ∧ p2) ∨ p4) → p5) → p4) → ((p5 → (True ∧ p1)) → ((p5 → p1) → (p2 ∨ (p5 ∨ (((p5 → False) → p2) ∨ True)))))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
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
theorem thm_5_vars_150253354118907131959682246070 : ((p3 → (((p1 ∧ (p2 → p3)) ∨ (p4 ∨ ((p4 → (p3 → p3)) ∧ p3))) → (True ∧ ((False ∧ False) ∨ True)))) ∨ ((True → p3) → (p3 ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206248580374315275316432097962 : ((False ∨ (((p4 → p4) ∧ p3) ∨ p1)) ∨ (((p5 ∧ p3) ∧ (((p2 ∨ p5) ∨ True) ∨ (True ∨ (False → (p4 → ((p5 → p3) ∨ p2)))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53487269106473963156369826327 : (((p4 ∧ (((p4 → True) ∨ False) ∧ (((True ∨ p3) → p3) ∧ True))) → ((p2 ∨ (((p1 ∨ p2) ∨ False) ∨ (False ∨ (True ∨ p2)))) ∧ p3)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h11.left
  let h13 := h11.right
  -- Disjunctions on the left can always be decomposed.
  cases h12
  case inl h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h13.left
    let h16 := h13.right
    -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
    have h17 : (True ∨ p3) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h15, we can now drive its conclusion.
    let h18 := h15 h17
    -- One of the premise coincides with the conclusion.
    exact h18
  case inr h19 =>
    -- False on the left can always be used.
    apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314480349585664707354772409797 : (p3 ∨ ((True ∧ ((p2 ∨ True) ∨ (((((((False → (p4 ∨ p1)) ∨ p5) ∧ p2) ∨ p2) ∧ p4) ∨ True) → False))) → ((p1 ∧ p4) ∨ (True ∨ p4)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113529706635258090037332696185 : (((((p5 ∧ (p3 → (p2 ∧ True))) → p4) ∧ (p2 → ((False ∧ False) ∧ ((True ∧ ((True ∨ False) → False)) → p1)))) ∨ (p2 → p2)) ∨ (False ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47070427377998446606432795351 : ((((p5 ∧ (((p5 ∨ ((False ∧ (p4 → (((p3 ∨ p1) → p2) ∨ p3))) → p3)) → (True ∨ True)) ∨ p1)) ∨ (p5 ∨ p5)) ∨ (p4 ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136060261912669234860017952563 : ((((True ∨ ((False ∧ p4) ∨ (p5 ∨ p1))) → False) ∧ (((p4 ∧ p4) ∧ (p4 ∨ (p2 ∨ (p5 → (p2 → False))))) → p3)) ∨ (p1 ∨ (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125538941914662622839767951507 : (((True → p4) ∧ ((((((p2 ∨ (p5 ∨ p2)) → ((p3 ∨ p4) ∨ p5)) ∧ False) ∧ (p2 → (p2 ∧ p5))) ∨ p4) → (True ∧ p3))) → (p4 ∧ p4)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h9 := h6 h8
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64110798127551826629730190323 : ((False ∨ (((p4 ∧ p1) → (p1 ∧ ((p5 ∧ p5) ∧ p5))) → ((((p5 → (True ∧ p1)) → p4) ∧ True) ∨ ((p4 → p2) → (p4 → p4))))) ∨ p2) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141147351792964601874467397057 : ((((p1 ∨ (False ∧ p2)) ∨ (p2 ∧ False)) ∧ ((((p5 ∨ (False ∧ False)) ∨ p5) ∨ ((False ∧ (p1 ∨ False)) ∨ p1)) ∨ p1)) → ((False ∨ p3) ∨ p1)) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- Disjunctions on the left can always be decomposed.
          cases h7
          case inl h8 =>
            -- Disjunctions on the left can always be decomposed.
            cases h8
            case inl h9 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h5
            case inr h10 =>
              -- Conjunctions on the left can always be decomposed.
              let h11 := h10.left
              let h12 := h10.right
              -- False on the left can always be used.
              apply False.elim h11
          case inr h13 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h5
        case inr h14 =>
          -- Disjunctions on the left can always be decomposed.
          cases h14
          case inl h15 =>
            -- Conjunctions on the left can always be decomposed.
            let h16 := h15.left
            let h17 := h15.right
            -- False on the left can always be used.
            apply False.elim h16
          case inr h18 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h18
      case inr h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h19
    case inr h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- False on the left can always be used.
      apply False.elim h21
  case inr h23 =>
    -- Conjunctions on the left can always be decomposed.
    let h24 := h23.left
    let h25 := h23.right
    -- False on the left can always be used.
    apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172633922913383671023480960893 : (((p5 ∧ False) ∧ ((p3 ∨ (((p4 → (True ∧ (False ∨ p3))) → p2) ∨ False)) ∧ p1)) ∨ (p1 ∨ (p1 → ((p1 ∨ p2) ∨ ((p2 → p1) → p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704274658201638341591334531516 : (((((((p1 ∧ p3) ∨ p5) → p3) ∧ ((False → p2) ∧ p2)) → ((True → (p2 → (p1 ∨ ((p5 → p2) ∧ ((p4 ∧ False) ∨ p2))))) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135879712104752733287944318600 : (((True ∧ (p1 → ((p1 ∧ ((True ∨ True) → False)) ∧ (p2 ∨ p5)))) ∨ (p5 ∨ (True ∧ (((True ∧ p2) → True) ∨ p4)))) ∨ ((p3 → p5) → p5)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43372924809939725097647931367 : (((((((p2 ∨ ((p3 → p5) ∧ (p2 → False))) → ((p1 ∨ p2) ∨ (p5 → (p2 → p1)))) → p3) ∧ ((p5 ∧ p5) ∧ p1)) ∨ True) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322618573382670352898352893560 : (p5 ∨ ((p5 → ((p1 ∨ (p1 ∧ (p1 ∧ (p1 → (((p5 ∨ p5) ∨ True) ∧ p2))))) → ((p4 → p3) → ((p2 ∧ (p2 → p1)) ∧ p1)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178377433794507253497716414885 : ((((p4 ∨ (p4 ∨ (p1 → (True → (p4 ∧ p5))))) ∨ p3) → (p4 ∧ p5)) ∨ (p5 → ((False → (p5 ∧ p4)) ∨ ((p1 → (True → p5)) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198457912492033928245267964814 : ((p5 ∧ ((p1 ∧ p3) ∧ ((p4 ∨ p2) → p1))) ∨ (((p3 ∨ True) ∨ ((p4 ∧ p3) ∨ (((p5 ∨ p2) → p3) → (p4 ∨ p2)))) ∨ (True ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324975290074714076480267541796 : (p5 ∨ ((p1 → p2) ∨ (((((False → p1) ∧ (p3 ∨ p5)) ∨ p3) ∧ ((p4 ∨ p1) → (p2 ∨ (((p2 ∧ (p2 ∨ p2)) ∧ p1) ∨ True)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347109214521056586781313521313 : (p3 → ((((True ∧ (p2 ∧ True)) ∨ p1) ∧ ((p1 ∧ (p2 → False)) ∨ (p5 ∨ p5))) ∨ ((((p2 ∨ p3) ∧ p3) ∨ (p5 → p2)) ∧ (p5 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682866334386550180882220751112 : (((((p3 → (p1 ∧ p3)) → (((p2 ∧ ((p3 ∨ p4) ∨ (p5 → (p1 → p3)))) → p3) ∨ True)) ∧ (((p1 ∧ p3) ∧ p3) → (p1 ∧ p1))) ∨ p4) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
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
  exact h5
  -- Conjunctions on the left can always be decomposed.
  let h7 := h2.left
  let h8 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h7.left
  let h10 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179228279331579034332134616396 : ((p4 ∧ (False ∨ (p1 ∧ (p3 ∧ (((p4 ∧ p5) ∨ (True ∨ p4)) ∨ p2))))) ∨ ((p4 ∧ ((p1 ∧ p2) → p5)) → ((p2 → p4) ∨ (False ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114960753775184245915132525687 : (((p2 ∨ (p1 ∨ (p4 → ((p5 → (p5 ∨ p2)) ∧ (p2 ∨ (p5 ∧ p4)))))) → (p4 ∧ (((p1 → (p2 ∨ True)) ∨ False) → p3))) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318384529732061788013224844158 : (p4 ∨ ((True → (((False → False) → (((p2 → p2) → ((p5 → p2) ∧ p4)) ∨ (((False ∧ (p4 ∨ p5)) ∨ (p4 ∧ p3)) ∨ True))) ∧ p2)) → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_232180224117913554141355514265 : (((False → False) → True) → (True → (((p5 → ((p5 → (((p1 ∨ (p5 ∨ (p5 ∨ p1))) → p1) ∨ (False ∨ p1))) ∨ (False ∨ p5))) → p2) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305621330354906617204149624900 : (p1 ∨ ((((p1 ∧ True) ∧ p1) ∨ (((p5 → False) ∨ p5) ∨ (p2 ∨ p4))) → ((p3 ∨ p2) → (p3 → (((p5 ∧ True) ∨ (p3 ∨ True)) ∨ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h4
        case inr h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h13
      case inr h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h4
        case inr h16 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h4
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- Conjunctions on the left can always be decomposed.
      let h21 := h19.left
      let h22 := h19.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h23 =>
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h24 =>
        -- Disjunctions on the left can always be decomposed.
        cases h24
        case inl h25 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h26 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h26
      case inr h27 =>
        -- Disjunctions on the left can always be decomposed.
        cases h27
        case inl h28 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h29 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198345778767632015958342806920 : ((p2 ∧ ((p1 ∧ p3) ∧ ((True → p2) ∧ p1))) ∨ ((p5 ∧ False) → (p5 → ((True ∧ (p2 → p2)) → (((p1 ∨ p4) ∨ (True → p5)) ∨ p3))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50663530845000204251211878647 : ((((False ∨ (((p1 ∧ p2) ∨ p4) ∧ (True ∧ p2))) → (True ∨ (((p5 → p2) → p1) ∨ (False ∨ p2)))) → (p4 ∨ ((True ∧ False) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322565242347977757350407911642 : (p5 ∨ ((p3 ∨ ((((p1 ∧ (True ∨ ((False ∧ (((p4 ∨ (p3 → (p2 ∨ p4))) → p3) ∨ p1)) → p2))) ∧ (p4 ∨ p3)) ∧ p5) ∧ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111860062342225644552531551260 : (((((p3 ∧ ((p3 → p2) ∨ (((True ∧ (True ∨ False)) ∨ p3) → False))) → (p2 → False)) ∧ ((p1 → True) → (p3 → True))) ∨ p5) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38621415153206684699401509498 : (((((p2 → (True ∧ (True → (p2 ∨ p2)))) ∧ p1) ∨ ((((p3 ∨ p1) → p5) → p1) ∧ ((p5 ∨ p2) ∧ (p1 ∨ (p1 → p3))))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137331838763443759862692909161 : ((p2 ∧ (p4 ∧ (p3 ∧ (p2 → ((p2 ∨ (True → False)) → (p4 ∨ ((False ∧ p3) → ((False ∧ p1) ∧ (p2 ∨ False))))))))) ∨ ((p1 ∧ p2) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300151859575662235881963686967 : (False ∨ ((p3 ∨ (((True ∨ p2) → ((p2 → (((True → p2) ∧ p4) → p2)) → (p1 ∧ (p2 ∨ (p1 ∧ (False → False)))))) ∧ p1)) ∨ (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159189075959941376354002403421 : ((p1 → (p5 → (p3 ∨ (((p1 ∨ (((p3 ∧ True) ∨ False) ∧ p4)) ∧ False) ∧ (p2 ∧ (False ∧ p3)))))) ∨ (((p2 ∨ (p5 ∧ False)) → p2) ∨ False)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172812563876437018560079286817 : ((True ∧ ((True ∧ (((p1 ∧ True) ∨ ((p3 → False) → (True ∨ p3))) ∨ p3)) → False)) ∨ (p3 ∨ ((((p4 → p1) → False) → (p2 → True)) ∨ p2))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705301961751206413871556334083 : ((((((p4 ∧ (p4 ∨ (False ∨ p2))) ∧ False) ∨ p3) ∧ (p1 ∧ ((p3 → (False ∧ (p4 ∨ ((True → p1) → ((p2 → p5) → True))))) ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38974012730810871393723125509 : ((((p1 ∧ p4) ∧ (p3 ∧ (p2 ∨ (p2 ∧ (p2 → ((p3 ∨ (((p3 ∨ ((p4 ∧ (True ∧ p3)) ∨ p2)) ∨ p4) → p3)) → False)))))) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_634443123276266027398882428830 : (((((((((True → True) ∧ True) → (False → p5)) ∧ ((p5 → p3) → ((p4 ∨ False) → p2))) ∧ (p1 ∧ p1)) ∧ ((True ∧ p4) ∧ p1)) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136091374301427725635605742857 : ((((p5 ∧ ((p3 ∨ p4) ∨ (p5 ∧ p2))) ∧ p5) ∨ (p2 → ((((((p1 ∧ False) ∧ p1) ∨ p3) → True) → True) ∨ p5))) ∨ ((False → p4) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_688320301622442851100508243278 : (((((p4 ∨ True) → ((p5 ∨ True) ∧ ((p1 ∧ p5) → (p5 ∨ (p5 ∨ (p1 ∧ p1)))))) ∧ ((p2 ∨ (((p4 → p5) ∧ True) → p4)) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300587627464519508802911789264 : (False ∨ ((((((((True → p1) ∧ p5) ∨ (p2 → (p3 → (p3 ∧ True)))) → p1) → p4) ∧ (p1 ∧ p1)) → True) → ((True ∧ p4) → (p4 ∧ p4)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60721022587709104231614442334 : ((True ∧ ((p5 ∧ ((p5 → p1) ∨ (p5 ∨ False))) → (((p5 ∨ (((False ∨ True) ∨ True) → (p1 → p4))) ∧ p5) → ((False ∧ p3) ∨ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58790696695593190041767952034 : (((p5 → True) ∧ ((p1 ∧ (False ∨ (True → p2))) ∨ ((p1 → ((True → ((p2 ∨ (p1 ∧ p4)) → False)) ∧ p3)) ∨ (p5 → (p4 ∨ p5))))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137998115928469763211724718879 : ((p5 ∨ (p3 ∨ ((p2 ∨ ((((p1 ∨ ((True ∧ False) ∨ False)) ∨ p1) ∨ (False ∨ True)) ∨ p1)) ∨ ((p5 ∨ p2) ∨ p3)))) ∨ (p3 ∨ (p3 ∧ p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346634276677478028318716966620 : (p3 → ((p4 ∧ (((p5 ∧ ((p2 ∨ p3) ∧ ((False ∧ (((p2 ∨ p2) ∧ True) → False)) ∧ False))) → (p2 → p4)) → False)) ∨ (True ∨ (False ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347291067380934238742761009189 : (p3 → (((p1 → p4) ∨ (((p1 → p2) → (p1 ∨ p4)) ∧ p2)) ∨ ((False → True) ∨ (False ∧ (p5 ∧ ((((p2 → p5) ∧ p1) ∨ p2) ∧ p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68277287934864427494301483012 : ((p3 → (((((((p3 ∨ p5) ∨ False) ∧ p4) ∧ (p3 ∨ p2)) ∨ p4) ∧ (p1 ∨ (((p1 ∨ (True ∧ False)) → p3) ∧ p2))) → (False ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256450269251762602649312782877 : ((False ∨ p4) → ((((True → p1) ∧ (((p1 ∧ ((p3 → (((False → (False → (p2 → p5))) → p1) ∨ p3)) → p5)) ∨ False) → p5)) → p1) ∧ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h8 := h3 h7
    -- One of the premise coincides with the conclusion.
    exact h8
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_793121744715046990425376784121 : (((True → ((p2 → p5) → ((((p4 ∨ ((p4 ∧ (p3 → (((p1 ∨ p4) ∧ True) → p1))) ∧ True)) ∧ False) ∧ (p3 → p3)) ∨ (p2 ∨ True)))) ∨ False) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217305959686118295620977867251 : (((p5 ∧ (p3 ∨ p3)) ∨ p5) → ((((((False → ((p5 ∨ p3) ∧ p2)) → p3) ∧ p3) ∨ (p4 ∨ (True → p5))) ∧ ((p3 ∨ p5) → True)) ∧ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- One of the premise coincides with the conclusion.
    exact h9
  -- Implications on the right can always be decomposed.
  intro h11
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h16 =>
      -- One of the premise coincides with the conclusion.
      exact h13
  case inr h17 =>
    -- One of the premise coincides with the conclusion.
    exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354130683451593162347647117288 : (p4 → (p5 → (p3 → ((p4 ∧ True) ∧ ((False ∨ ((True ∨ (p5 ∨ (p1 ∧ (p3 ∨ p3)))) → (True ∧ (p5 ∧ (p1 ∧ (p1 ∧ True)))))) ∨ p3))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320991090043719104561049507548 : (p4 ∨ (False ∨ (((False → True) ∧ ((False ∧ (((p1 ∧ (p1 → p2)) → p1) ∧ (p2 ∨ (p5 → (p4 ∨ False))))) ∧ ((True ∧ p3) → p2))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356041721098611757229972027451 : (p5 → ((False ∧ (True ∧ (((p1 → p4) → (p2 ∧ (p3 ∨ (p1 ∧ p1)))) ∨ ((False → p2) → (p3 → p4))))) ∨ ((p3 ∧ p5) → (p2 ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_663040984917191020744309195203 : (((((p5 ∨ (p4 ∨ p3)) → ((((p3 ∨ ((True ∧ p1) ∨ True)) ∧ ((p5 → (p4 → (p4 ∨ True))) ∧ False)) ∧ True) ∨ True)) → (p5 ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135221515147621010255664382964 : (((((p1 ∨ ((p4 ∨ p2) → (p3 ∧ p3))) ∨ (False ∨ p2)) ∨ ((p1 → p2) ∧ (True → (True ∨ p3)))) → (p2 ∧ p4)) ∨ (False ∨ (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52543628640400057895690461115 : ((((((((p4 → p4) ∨ (p3 ∧ False)) → (p1 ∧ p5)) ∧ p2) ∨ True) → False) ∨ ((((p2 ∧ p3) ∧ p1) ∧ False) → ((p4 → p2) → p1))) ∨ False) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152387989166385076595721097679 : (((((p2 ∧ p4) → p5) ∨ p4) → (((True → ((((p1 → p1) → p5) ∧ p1) ∨ (p5 → p1))) ∨ p3) → False)) → (p4 ∨ (True → (p5 ∨ True)))) := by
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
theorem thm_5_vars_113419804173450188730550428409 : ((((((False ∧ p4) ∧ True) ∧ ((p5 → ((p5 → (p2 → p4)) ∧ p5)) ∨ ((True → p5) → (False → True)))) ∧ p4) ∨ (True ∧ p3)) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214783354238402978244584009184 : (((False ∨ p3) ∨ (True → p5)) ∨ ((((((p2 → False) ∧ p5) ∧ p2) → (((p5 ∨ ((p2 ∨ p2) → False)) → (False ∨ p3)) ∧ False)) ∧ True) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h8 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h9 := h6 h8
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h1.left
    let h12 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h11.left
    let h14 := h11.right
    -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
    have h15 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h12
    -- We have shown the premise of h13, we can now drive its conclusion.
    let h16 := h13 h15
    -- False on the left can always be used.
    apply False.elim h16
  -- Conjunctions on the left can always be decomposed.
  let h17 := h1.left
  let h18 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h19 := h17.left
  let h20 := h17.right
  -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
  have h21 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h18
  -- We have shown the premise of h19, we can now drive its conclusion.
  let h22 := h19 h21
  -- False on the left can always be used.
  apply False.elim h22
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349046770698052377783202163500 : (p3 → (p5 ∨ (((p2 ∨ p4) ∨ (p5 ∧ (((((p1 ∨ (p3 ∧ (False ∧ p4))) ∧ p5) → p5) → False) ∧ (p5 ∧ True)))) ∨ (True → (True ∧ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_379796474590423348006019314319 : (((((((p5 ∧ ((((p4 ∨ p5) ∧ (False ∨ (p1 → p1))) ∧ (False → p1)) ∨ (((p2 → p1) ∧ True) ∧ p1))) ∨ True) ∨ True) ∧ p3) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_134942441588707776899279144195 : ((((p4 ∧ ((p1 → ((p2 → p5) ∧ ((p4 ∧ (p2 ∨ p4)) ∧ (p2 ∨ p5)))) ∨ p1)) ∨ (p1 ∨ p2)) ∧ (p4 ∧ p3)) ∨ ((False ∧ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241304775680658929025701110367 : ((False → True) ∧ (((p2 ∨ p2) ∧ p1) → (((((p4 ∧ (((p1 ∨ p5) ∨ (True ∨ p4)) ∨ (True ∨ p2))) → p5) → p5) ∧ p2) ∨ (p1 → p2)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54715426598403167640355118835 : (((((p5 ∨ (p5 → p2)) → p2) → (p1 ∨ p4)) → (((p2 → (p5 → p1)) ∧ (p3 ∧ True)) ∧ ((p1 → p5) → (p2 ∨ (True → p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65201229928121942899597731112 : ((p3 ∨ ((((((True ∧ p1) ∧ True) ∨ (p3 ∨ p4)) → (p4 ∧ ((p2 → (False → p4)) → (False ∧ ((p2 → True) → p3))))) ∨ p2) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



