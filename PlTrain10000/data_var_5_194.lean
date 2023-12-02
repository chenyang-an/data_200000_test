variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200285866789376407359898518913 : (((p4 → (p2 ∧ p1)) → ((p5 → True) ∨ False)) → (True ∧ ((p1 ∧ (p3 ∨ (p2 ∧ (p5 ∧ (False ∨ (p3 → (p3 ∧ (p3 → True)))))))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215387025219179658315923779600 : ((p2 ∧ (p2 ∧ (p1 ∧ p2))) ∨ (((p3 ∨ False) ∧ (p4 ∧ p5)) ∨ (p1 ∨ (((((p1 ∨ True) ∨ False) ∧ p2) ∨ (p2 → (False → p2))) → True)))) := by
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
theorem thm_5_vars_664266700294358066837893966795 : ((((p1 ∨ (p1 ∧ ((p3 ∧ p1) → (p4 ∨ (((p4 ∨ (False ∨ (p2 → ((p2 ∧ p1) ∨ p5)))) → p5) ∧ (p3 → p3)))))) → (True → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114053733083497967749474839113 : (((((((False ∧ (p5 ∨ ((p2 → False) ∨ p2))) ∨ False) ∧ (p5 ∧ p1)) → p2) → ((p5 ∨ False) ∨ p2)) ∨ ((p2 → p4) ∨ p1)) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112585713443670743419631367243 : ((((((((p2 ∧ (p1 ∧ p2)) → p2) → True) ∨ ((p2 → p5) → ((p2 ∧ (p2 ∧ p1)) ∧ p2))) → p5) ∧ (p1 ∧ p4)) → False) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_77978092782947181582551677481 : (((p3 ∨ (p1 → (p3 ∨ (((p2 → (True ∧ ((p1 ∧ p5) → p5))) → (False ∧ (p5 → p1))) → ((p5 ∧ (p1 ∨ p4)) ∨ False))))) → False) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 ∨ (p1 → (p3 ∨ (((p2 → (True ∧ ((p1 ∧ p5) → p5))) → (False ∧ (p5 → p1))) → ((p5 ∧ (p1 ∨ p4)) ∨ False))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : (p2 → (True ∧ ((p1 ∧ p5) → p5))) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h10 := h4 h5
    -- We need to get the left conjuct of h10 based on <expert-advice>.
    let h11 := h10.left
    -- False on the left can always be used.
    apply False.elim h11
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h12 := h1 h2
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171547413275939376372955948946 : (((((((p3 ∧ False) ∨ (p5 → True)) ∧ ((True ∨ False) ∨ p3)) ∨ p1) → False) ∨ p4) ∨ (False → (True ∨ (False → ((p4 ∧ (p5 → p3)) → p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_798526510502009281520892872298 : (((p1 → ((False ∨ ((p5 → p4) ∧ ((p5 ∧ p2) ∧ False))) ∨ (((False → p1) → (p5 → (p3 ∨ (p3 → (p5 ∨ (p2 → True)))))) ∧ p1))) ∨ p3) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307205044611816241257411264773 : (p1 ∨ (p1 ∨ (((p4 → ((p1 → (p1 ∧ p5)) ∨ p4)) ∧ True) ∧ ((p5 → ((((p2 ∧ p3) → True) ∧ ((p5 → False) ∧ p3)) ∨ True)) ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142985829020622194881123048802 : ((True → (((p3 → (p2 ∧ (p4 → ((p2 ∧ True) ∨ p3)))) → ((False ∨ p2) → (p2 ∧ (True ∨ False)))) ∧ (True ∧ False))) → ((p5 ∧ True) ∨ False)) := by
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
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153535546457244582962785399008 : ((True → (((((True → p2) ∨ False) ∧ ((p2 → p2) → p3)) → ((p5 ∧ False) ∨ p3)) ∨ ((False → p2) ∧ p4))) → ((p2 ∨ (False ∨ True)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253637662682922415300114609106 : ((p1 ∧ True) → ((p2 ∨ p3) → ((p3 ∨ ((((True ∨ (p4 → False)) → ((p4 → p4) ∨ (p4 ∧ p3))) → p4) → (p1 ∧ p3))) ∨ (True ∨ p5)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h1.left
    let h8 := h1.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53824631948803301960881745015 : ((((True → ((p5 ∧ False) ∨ (p3 ∨ p5))) ∨ (p4 ∧ p5)) ∨ ((True ∨ ((p3 ∨ (p1 → True)) → ((p3 ∧ (p1 ∧ p5)) → p3))) ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54575953678919850287340410873 : (((p1 ∨ ((((False → p1) ∧ p4) → p4) → p2)) ∨ (((p3 → p4) ∨ (((((p5 ∧ p3) ∧ (p5 → p1)) → p2) ∧ p5) ∧ p5)) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_94088740499227196158781532013 : ((p1 ∧ (p1 → (((p2 ∧ (p5 ∨ (((((p3 ∧ p1) ∧ (False → p2)) ∧ p4) → p1) ∨ (p1 → False)))) → (True ∧ (p3 → p3))) ∧ False))) → False) := by
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
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748323585736268602188319333667 : ((((p2 → p1) → (((p1 ∨ p1) ∨ p1) ∧ (((((p5 ∨ False) ∨ (((p1 ∧ p4) → p3) → ((p4 → p4) ∨ False))) ∨ p4) ∨ True) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52532977188891489618578284747 : (((((p2 ∧ p3) ∧ (False ∨ (True ∧ (True ∨ ((False → True) → True))))) ∨ p2) ∨ (True ∧ ((True ∧ (p3 ∧ p3)) ∨ (p5 → (p1 ∨ p5))))) ∨ p5) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41673033849489268002543613038 : (((((p2 ∨ ((False ∨ p3) ∨ p4)) → p3) ∨ ((p4 ∧ ((False → p5) → p1)) ∧ ((p1 → (p3 → p1)) ∧ (True → (p1 ∧ True))))) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142467991868440818395744214967 : ((p5 ∧ (((((p2 ∨ True) ∨ p4) ∧ (True → (p3 → (p2 ∧ p2)))) ∨ False) → ((((p2 ∧ p4) ∨ False) → p3) ∧ False))) → (p2 → (False ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : ((((p2 ∨ True) ∨ p4) ∧ (True → (p3 → (p2 ∧ p2)))) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h8 := h4 h5
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
  have h12 : ((((p2 ∨ True) ∨ p4) ∧ (True → (p3 → (p2 ∧ p2)))) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
    -- Implications on the right can always be decomposed.
    intro h13
    -- Implications on the right can always be decomposed.
    intro h14
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h11, we can now drive its conclusion.
  let h15 := h11 h12
  -- We need to get the right conjuct of h15 based on <expert-advice>.
  let h16 := h15.right
  -- False on the left can always be used.
  apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42879774342769359651372149381 : (((p3 → (((((((p1 ∧ False) ∨ p1) ∧ (p1 ∨ True)) ∨ (p3 → (((False ∨ p3) ∧ p4) → (p2 ∨ p2)))) → p1) ∨ p1) ∧ p3)) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612226590557013080085423520520 : ((((((p4 ∨ (True ∧ True)) ∧ ((((p2 ∨ p3) → (False ∨ p4)) → (p1 ∧ p5)) ∧ (((p4 ∧ p3) → p1) ∨ p5))) ∧ (True ∧ p4)) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_50204737272511252405334941864 : ((((((p2 ∧ p5) ∧ (((p4 ∨ p1) ∨ p5) → (p5 ∨ (p4 → ((p1 ∧ p3) ∨ p5))))) ∨ p5) ∨ p5) ∨ (p5 → (p5 ∧ (p5 ∧ p5)))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337538590599953892459275464552 : (p1 → (((p3 ∨ ((((True ∨ p4) ∨ p4) ∨ p3) → False)) ∨ (True ∨ (p3 ∨ (False → (p5 ∨ (p5 → p4)))))) ∨ ((p5 → (p5 ∨ False)) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54506557881606319072278647064 : ((((p3 ∨ (p1 ∧ p4)) ∨ ((True → p4) ∧ p4)) ∨ (True → ((((False ∨ (p5 ∧ (p4 → (p3 ∨ p2)))) ∧ (False ∨ p2)) ∨ True) ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256016040715321842678501780173 : ((True ∨ p3) → (p3 ∨ ((((p3 → p4) → ((p2 ∧ (p3 ∨ True)) ∨ (True ∧ (p1 → p1)))) → (p4 ∧ (p2 → False))) ∨ ((False ∧ p1) → p3)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181698007656121094508469823479 : ((p5 → (((True → (((False → p5) ∧ p1) → True)) ∨ (True → p4)) → False)) → ((p2 → (p3 ∨ (p2 → ((False ∧ (p1 ∨ p5)) ∧ p2)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684008522308916308535907451044 : (((((((p2 → p1) ∨ True) ∧ (((p2 ∧ ((p4 → True) ∨ p2)) ∧ (True ∨ p5)) → p2)) → p4) ∨ (True ∨ (((p4 → p1) ∧ p2) → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215759708585169647747743005214 : ((p1 ∨ ((p4 ∧ p2) ∨ False)) ∨ (p5 → ((True ∧ ((True ∨ p4) → (p2 ∨ ((((True ∧ (p2 ∧ False)) ∧ p4) ∨ True) ∨ (p3 ∨ p4))))) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258964054472562730901569558865 : ((True → p3) → (((p2 ∨ ((p4 → p2) ∨ False)) → ((True → (p5 → (p4 ∨ (p1 ∧ p1)))) ∧ (p2 → p5))) ∨ ((p3 ∧ True) ∧ (p4 → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343238524571290121516189921215 : (p2 → ((p1 ∨ (p5 ∧ p5)) → (((p5 ∨ (p4 → ((False → p1) ∨ (True ∨ p3)))) ∨ (False ∧ p4)) → (((p5 → p3) ∨ (p4 ∨ True)) ∧ True)))) := by
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
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h2
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h2
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- False on the left can always be used.
    apply False.elim h16
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172478344660064630000738550958 : (((((True → True) → p3) → p2) → ((p3 ∨ (p4 → ((p2 ∨ p5) ∨ p2))) ∧ p3)) ∨ ((p2 ∧ p4) → (p4 ∧ ((p5 → p4) ∨ (False → p2))))) := by
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
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51585701254995294027710672071 : (((True → (p5 ∨ ((p2 ∧ p4) ∨ ((False ∧ (((p3 ∧ p5) ∨ p3) ∧ p3)) ∨ (p1 ∨ p3))))) → ((p2 ∧ p2) ∨ ((p3 ∧ p3) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263835132974635144383547457891 : (True ∧ ((((p1 ∨ p4) ∧ p3) ∧ (((p2 ∧ (p1 → (True ∨ True))) ∧ (p1 ∨ p5)) ∨ p4)) → ((((p3 → (p3 → False)) ∧ p2) ∨ False) → p1))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    let h6 := h1.left
    let h7 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- Conjunctions on the left can always be decomposed.
        let h14 := h12.left
        let h15 := h12.right
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h16 =>
          -- One of the premise coincides with the conclusion.
          exact h16
        case inr h17 =>
          -- One of the premise coincides with the conclusion.
          exact h10
      case inr h18 =>
        -- One of the premise coincides with the conclusion.
        exact h10
    case inr h19 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h20 =>
        -- Conjunctions on the left can always be decomposed.
        let h21 := h20.left
        let h22 := h20.right
        -- Conjunctions on the left can always be decomposed.
        let h23 := h21.left
        let h24 := h21.right
        -- Disjunctions on the left can always be decomposed.
        cases h22
        case inl h25 =>
          -- One of the premise coincides with the conclusion.
          exact h25
        case inr h26 =>
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h27 : p3 := by
            -- One of the premise coincides with the conclusion.
            exact h9
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h28 := h4 h27
          -- We want to use the implication h28 based on <expert-advice>. So we show its premise.
          have h29 : p3 := by
            -- One of the premise coincides with the conclusion.
            exact h9
          -- We have shown the premise of h28, we can now drive its conclusion.
          let h30 := h28 h29
          -- False on the left can always be used.
          apply False.elim h30
      case inr h31 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h32 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h9
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h33 := h4 h32
        -- We want to use the implication h33 based on <expert-advice>. So we show its premise.
        have h34 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h9
        -- We have shown the premise of h33, we can now drive its conclusion.
        let h35 := h33 h34
        -- False on the left can always be used.
        apply False.elim h35
  case inr h36 =>
    -- False on the left can always be used.
    apply False.elim h36



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191910008402301649575392234979 : ((p5 ∨ (True ∧ ((p5 ∨ (p2 ∧ (p4 ∧ p2))) ∨ True))) ∨ (((p2 ∨ ((p5 ∧ ((p5 → p2) → (p5 ∨ True))) ∧ p1)) → p3) ∧ (False ∨ True))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179232318830972032070736721771 : ((p4 ∧ (p3 → ((((p1 → p5) ∧ (p5 → p1)) ∨ (False ∨ True)) ∨ p4))) ∨ (p4 ∨ (True ∨ (p2 ∧ ((p3 → p2) ∧ ((False → p3) → p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345732706712050833520769471205 : (p3 → ((p5 → ((((p1 → (p5 ∨ (p3 ∧ True))) → ((True ∨ p4) ∨ ((p2 → p1) ∧ p3))) → (p4 ∨ (True ∧ p4))) ∧ (False ∧ True))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112791954075634372826503719777 : ((((p4 → (True ∨ ((p5 → p4) ∨ (p1 → p1)))) → ((p2 ∨ (((p4 ∨ p1) → True) ∧ (p1 ∨ p2))) ∨ (False ∨ p4))) → False) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_591774008212239694497897828713 : (((((((False → p1) → (p2 ∨ ((p2 ∨ ((((True → p4) ∧ p1) → p3) → (p3 → p1))) ∨ False))) ∧ (p4 ∨ p5)) ∨ (p1 ∨ p3)) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620170240782456603307433152585 : (((((p2 ∧ p2) ∨ (p3 ∧ ((((False → p1) ∨ ((p1 ∨ (p4 ∨ (p2 ∧ p2))) ∧ p2)) → ((p5 → p3) → p5)) ∨ (False ∧ p4)))) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_660003525308704895514690174849 : (((((((p5 ∧ (((p3 ∨ p5) ∨ False) → ((False ∨ (True ∨ (((p4 ∨ False) ∧ p1) ∧ p2))) ∧ True))) → False) → p2) ∨ True) → (True ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185941630751412001914777646836 : ((((True → p1) ∧ ((p4 ∨ True) → ((p1 ∧ False) → True))) ∧ p3) → (((((p1 ∧ (True → True)) ∨ p1) ∧ (p3 → p4)) → False) → (p4 → False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h8 : (((p1 ∧ (True → True)) ∨ p1) ∧ (p3 → p4)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h10 := h6 h9
    -- One of the premise coincides with the conclusion.
    exact h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h12 := h2 h8
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193703865838625264179515231550 : ((p1 ∧ (p1 → (p4 → ((False → p5) ∨ (p3 → p5))))) → ((True ∧ (p1 ∧ (p3 → p1))) → (False ∨ (p4 ∨ ((True ∧ (p3 → p2)) ∨ True))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119431501876689056094109389807 : ((p4 → ((((p2 ∨ ((p3 ∨ (((p5 → True) ∨ p1) → (p5 → True))) ∨ (p1 ∧ p5))) ∨ True) → p1) ∨ ((p3 ∧ p5) → True))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174036425760909663557500813492 : (((p3 ∨ ((False ∧ p4) ∧ (((False ∧ False) ∧ (p4 ∨ False)) ∨ (False ∧ False)))) → p1) → ((True ∧ p5) → (((p1 → (p2 ∧ p5)) ∨ p5) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_604005873168619357677805445168 : ((((p5 ∨ ((((p5 ∨ ((((p4 ∨ (True ∧ False)) ∨ True) ∧ p2) → p3)) → False) → ((p1 → (p2 ∨ p1)) ∨ p5)) → (p4 ∧ p5))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618326799977687975095347261059 : (((((p1 ∧ ((False ∨ p4) ∧ True)) ∨ ((((p5 → False) ∨ (((p1 → (p1 ∨ p2)) → p4) → (p2 ∧ p1))) → (False ∨ True)) ∨ p1)) ∨ p5) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_734518701621879757295331814587 : ((((p1 ∨ False) ∧ (p4 ∨ ((((p3 ∨ (p2 ∨ ((p2 ∨ (p2 ∨ p5)) ∨ ((p1 ∨ p4) ∨ False)))) → p3) → ((False ∧ p2) ∧ p3)) ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354606046606099762085219449983 : (p5 → ((((((p1 → False) ∨ (True → (p2 ∨ (True → ((p2 ∧ False) → p2))))) ∧ (((p3 ∨ (True → p3)) ∨ p2) ∧ p1)) → p4) ∨ p5) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2280621112118671273796359066 : ((((p4 → p1) ∨ ((p1 ∧ p5) ∧ (p3 → (p2 ∨ p4)))) → (p3 → p2)) ∨ (False → (((((True ∨ p2) ∧ False) → False) ∧ p5) ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h4
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337652701875908003947932192674 : (p1 → (((p5 ∨ (((True ∧ ((p1 ∧ (False ∧ ((True → True) → p3))) ∨ p4)) ∨ p4) ∨ p1)) ∨ p5) ∨ ((p3 → True) ∨ ((p5 → p5) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354723279056622625952349746441 : (p5 → (((((((True → (p1 ∨ (p4 → p3))) ∨ ((p2 ∨ p4) ∨ (False ∧ True))) → False) → p4) ∨ (p2 → p2)) → ((p3 ∧ p1) ∨ p5)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340393782506079728097862065270 : (p2 → ((((((False ∨ (p3 → (((p5 → (False ∨ p2)) ∧ (p2 → ((p5 ∨ p5) ∨ p4))) ∧ p3))) ∧ p1) → p5) ∨ p3) ∨ (p2 ∨ False)) ∧ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186290612188181243851714910604 : ((((((p4 ∨ p4) → True) ∧ (True → (False ∧ p1))) → p4) → p2) → (p1 → (p1 ∨ (((p1 ∨ True) ∨ ((p1 → False) → (p2 ∨ p3))) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
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
theorem thm_5_vars_54394758012161852054216533439 : ((((((p3 ∨ (p3 ∨ p5)) ∨ False) ∨ p1) ∧ p2) ∨ (True ∨ (True ∨ ((False → (False ∨ (p3 ∧ p1))) → ((p3 ∨ p2) → (p5 → p4)))))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248591411317441204192279576207 : ((p3 ∨ False) ∨ (((p4 ∧ p1) ∧ True) ∨ (((p4 ∨ p4) → ((p4 → ((p4 ∧ p3) ∧ (p2 ∧ True))) ∨ p5)) → (p1 → (False ∨ (p1 ∨ p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_8182496523679536768254574043 : ((((p5 ∨ ((((p1 ∨ (True ∧ ((p5 ∨ (p1 → (p5 ∧ p5))) → p4))) ∧ (True → False)) ∧ (p1 ∧ (True ∨ p4))) ∨ p4)) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_309812522237297196928471755402 : (p2 ∨ ((p2 ∧ (True ∧ (True ∧ ((((p5 ∧ p2) ∨ p1) → ((False → p2) ∨ True)) → ((p1 ∧ p3) → p4))))) ∨ ((p3 ∧ p4) → (p3 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312439901550640091272740528348 : (p2 ∨ (p4 → (((p5 → p4) → (p4 → p5)) → (p4 ∧ ((True ∧ p5) ∨ ((((p3 ∨ p1) ∨ p2) ∨ ((p3 ∨ p5) ∨ (p2 ∧ True))) ∨ p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
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
theorem thm_5_vars_51265602638637245133083470123 : ((((True ∨ p3) → ((((p1 ∧ (p3 ∧ (True → (p2 ∧ p1)))) → p4) → (p4 → p4)) → p1)) ∨ (p3 ∧ (True ∨ ((p5 ∨ True) ∨ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304733505189106109286960039967 : (p1 ∨ ((((p1 ∨ True) → ((p4 → p4) ∧ (p2 ∧ False))) ∧ (p1 ∨ (p2 ∨ ((((p5 ∨ p1) ∨ (p5 → p4)) ∨ p4) → p3)))) ∨ (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720668053388234694625600443313 : ((((((True ∧ p2) → False) → False) → (True → (((((p2 → True) → p4) ∧ (p2 ∨ False)) ∧ (False → (True → (p1 → (p3 → p2))))) ∨ True))) ∨ p5) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_596596348403774643518408572821 : (((((False → (p1 → ((p4 ∨ (p1 ∨ p4)) → p3))) → ((True ∧ p1) ∧ (((p1 → ((p4 ∧ p4) ∨ False)) ∧ p3) ∨ (p4 ∨ p4)))) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62512007320679042457705050782 : ((p3 ∧ (p3 ∧ (((False ∧ p2) ∧ (((p4 ∧ ((False → p1) ∨ (False ∧ p4))) ∨ (p1 → (p2 ∨ p1))) ∧ p2)) ∧ (True ∨ (p2 ∧ True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353722687969424775693579604074 : (p4 → (True → (((p2 ∨ p4) → (((((p3 ∧ (False ∧ (p5 → p2))) ∧ False) ∧ p5) → (p1 ∧ (True ∨ (False ∧ (p4 ∨ p5))))) ∧ False)) → False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p2 ∨ p4) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48850558364823768229045261662 : (((p2 ∨ ((p3 → (p5 → ((p2 ∨ True) → (p2 → p1)))) → ((False ∧ True) ∧ ((True ∨ p5) → (p4 ∧ p1))))) ∧ ((True ∨ p5) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_623610086899161013086359343755 : ((((False ∨ (p5 ∨ (((p4 ∧ (((p4 ∨ p4) ∨ (p3 → p5)) ∨ (((p5 ∧ p2) ∧ (p2 ∧ p5)) ∧ (p4 ∨ False)))) ∧ p2) ∨ True))) ∨ p1) ∨ p3) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40004279869696153261368317969 : (((p5 → ((((False ∨ p1) ∧ p3) → (p2 ∧ p3)) → (p1 ∧ (((p5 ∨ True) ∨ ((p4 → p1) → ((False ∧ False) ∨ False))) → p1)))) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51871231176010410480287462042 : (((((False → False) ∧ (((False ∧ (p2 ∧ True)) → p1) → ((p2 ∨ True) ∧ p3))) ∨ p4) ∨ (p2 → (p1 ∨ ((p3 ∨ p5) ∨ (p3 → p3))))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_46888809803940860801196529853 : ((((((False ∧ p5) ∧ (True → (((p5 ∨ (p2 → p2)) → p5) → (p4 ∨ ((p2 ∧ (p2 ∧ p2)) → p1))))) ∨ p3) ∨ True) ∨ (False ∧ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60770945555396388003150320645 : ((True ∧ ((p3 ∨ p1) ∨ (True ∧ ((((p3 ∨ (p5 ∧ p2)) → (True → (p4 → False))) → (True ∧ ((p3 ∨ p5) ∧ p4))) ∧ (p3 ∧ True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59369448727415561504206268420 : (((p5 ∨ p4) ∨ (((p3 ∨ (((True ∧ p3) ∨ p1) → (p4 ∧ p4))) ∧ p5) → (((p3 → (p1 ∧ p5)) ∧ False) ∨ (True ∨ (p4 → p4))))) ∨ False) := by
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
  cases h2
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_18430361919070707650579058363 : (((True → (((p4 ∨ (((False ∧ False) ∧ True) → ((p5 ∧ ((True → p4) → p3)) ∨ False))) ∧ False) ∧ p3)) → ((False ∨ p3) → (p5 ∧ p4))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h6 := h1 h5
    -- We need to get the left conjuct of h6 based on <expert-advice>.
    let h7 := h6.left
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- False on the left can always be used.
    apply False.elim h8
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h11 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h12 := h1 h11
    -- We need to get the left conjuct of h12 based on <expert-advice>.
    let h13 := h12.left
    -- We need to get the right conjuct of h13 based on <expert-advice>.
    let h14 := h13.right
    -- False on the left can always be used.
    apply False.elim h14
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337209761454246765468179608091 : (p1 → (((((True ∧ ((True ∨ (p1 → False)) ∧ p1)) → p2) → p2) ∧ ((p1 ∧ p5) ∧ (((p3 ∧ (p1 ∨ p2)) ∧ p5) → True))) → (p2 ∨ p5))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_800000361020872672374910773017 : (((p2 → ((((p4 ∨ p4) ∧ ((p3 → True) ∧ ((p1 ∧ (p5 ∧ p1)) ∧ ((p1 → (p5 ∨ False)) ∧ (p2 ∧ p2))))) ∨ (False → p4)) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51585201141432917097322544228 : (((True → (p2 ∧ (p2 ∧ (((p2 ∨ ((p5 ∧ (p1 → (p4 ∨ False))) → p3)) ∧ p4) ∧ p3)))) → (p1 → (p1 → (p3 ∨ (p3 → p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_784884614686092330513569547634 : (((p3 ∨ (p2 → (((False ∧ (True → p3)) ∨ (p2 ∨ ((p2 → (((False ∨ p1) ∧ ((p5 ∧ (True ∨ p3)) → p3)) ∨ p2)) → p4))) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231031884800644308510651707836 : (((p5 ∧ p5) ∨ p5) → ((p3 ∧ ((((p1 ∨ ((True ∧ p2) → ((True ∨ True) ∨ False))) → True) ∧ (p3 ∧ p2)) ∧ p4)) ∨ (p5 ∨ (True ∧ True)))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307182046655127423863050760621 : (p1 ∨ (p1 ∨ (((((p3 ∨ (p4 → p1)) → p2) → False) ∨ ((((p2 → ((p5 ∨ p1) ∨ True)) ∨ False) → (p5 ∨ p1)) → (False → p3))) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190101408454349051630184242629 : (((((p5 ∧ (True ∨ p3)) ∨ p2) → (True ∨ p2)) ∧ p2) ∨ ((((p3 → True) ∨ False) ∧ (True ∨ p4)) → ((p2 ∧ (p3 ∨ p4)) ∨ (False → p5)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h8
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225476074153740743532878313239 : (((p4 ∨ p4) ∧ p5) ∨ ((p3 ∨ (p3 ∨ ((p4 ∧ p5) → (False → (p1 → (((((True → p2) ∨ (False ∨ p2)) ∨ p1) ∧ p1) ∨ False)))))) ∨ p2)) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_203880649500397281921065795453 : ((p1 → (((p3 ∧ p4) ∧ False) → p2)) ∧ ((((((p2 ∨ (True ∧ (p5 ∧ p4))) → (p3 ∨ p3)) ∨ (True ∨ p4)) ∧ (p5 ∨ False)) ∨ True) ∨ p4)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- False on the left can always be used.
  apply False.elim h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59918489807857512915034007635 : (((p5 ∧ p4) → ((((p1 ∧ (False ∨ (False ∧ p5))) → p3) → (((p1 ∨ (p5 → False)) ∨ p5) ∧ (((False ∧ p2) → True) ∨ p4))) ∨ p3)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40205011795695968062354899736 : (((((p4 → p2) ∧ ((p4 ∨ (p2 ∨ p1)) → ((p2 ∨ (((p1 → (True ∧ True)) → p2) ∨ True)) → ((p1 ∧ p3) ∨ p4)))) ∧ False) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184137044898946359702308255409 : (((p4 ∧ (((((False ∨ p2) ∧ p4) ∧ p1) ∨ p5) ∧ p3)) ∨ True) ∨ (p3 ∨ ((((True ∨ p3) → False) ∧ (True ∧ (p4 ∧ p3))) → (p5 ∨ False)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711091961907073517115467421145 : ((((False ∧ (((p2 ∨ p2) → p5) ∧ True)) ∧ ((p3 → ((p2 ∧ (((p1 ∧ True) → p1) → p3)) → p3)) → ((p5 ∧ (True ∨ p3)) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_589420666840636627532387839274 : (((((((p5 → ((p4 ∧ p5) → (False → p5))) ∨ (((True ∧ ((True → False) → p2)) → (p1 ∧ False)) ∧ (True ∧ p5))) ∨ True) → p3) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329749382432414927884984932318 : (True → (True ∧ (((((False ∧ (p5 ∨ p1)) ∨ ((((p4 ∧ (p2 → p3)) ∧ p4) → (p4 → True)) → (True → p1))) ∨ p1) ∨ (p3 ∧ False)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_600835084490241149511573939594 : ((((False ∧ (False ∨ (p1 ∧ ((((((p4 → False) ∨ p5) ∧ ((p3 → ((p4 ∧ p5) ∧ p1)) → p5)) → p5) ∨ p1) ∨ (False ∧ p3))))) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156951105344652624230009629627 : ((((p5 → (p4 ∨ (((True ∨ p5) ∧ p2) → (p2 ∧ ((True ∧ p3) → p5))))) → (p3 ∧ True)) ∨ True) ∨ (True ∨ ((p2 ∧ (False ∧ p1)) ∨ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147548581349869587006371535605 : (((p4 → (((p4 ∧ p2) → (True → p4)) → (((True → p2) ∧ (((p2 ∧ p5) → p5) ∧ p5)) ∨ p3))) ∨ p1) ∨ ((True ∨ p5) → (True ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41534269548479459695823550698 : (((((True ∧ ((((p3 → p4) ∨ p4) ∨ p3) ∧ p4)) ∨ p2) ∨ ((p4 ∨ ((True ∨ (p5 ∧ (p2 ∨ (True ∨ True)))) → p3)) ∨ True)) ∨ p1) ∨ p5) := by
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
theorem thm_5_vars_64255931882324556017266237364 : ((False ∨ (p4 ∨ ((((((p2 ∧ (p2 → (p5 → ((False ∨ p3) ∧ p5)))) ∧ p5) ∨ (p3 ∧ ((p4 ∨ p5) ∨ p2))) ∨ p3) ∨ True) ∨ p1))) ∨ False) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149993052584678092757911597989 : ((p4 ∨ (p3 ∨ (p2 → ((p5 → ((p1 ∨ p3) ∧ ((p3 → (p2 ∨ p4)) ∨ (p2 → (p5 ∧ p1))))) ∧ p5)))) ∨ ((False ∧ p5) ∨ (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314541418435993692420195497233 : (p3 ∨ (((p4 → (p4 → ((((p2 ∧ True) ∧ (p4 ∨ (p1 ∨ (p3 → p3)))) → p4) ∧ p1))) → p5) ∨ ((p3 ∨ ((p1 ∧ False) ∧ p5)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158462184504283059331446468635 : (((p1 → p3) ∨ ((p4 → ((p1 ∨ (p1 ∧ (p3 ∨ True))) ∨ (p5 ∧ ((p2 ∨ p3) → p4)))) → p4)) ∨ (((p2 → p4) ∨ True) ∨ (p1 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_493670941203771012013170914775 : (((((p4 ∨ (p1 → p2)) ∧ p1) → ((p5 ∨ ((((p3 ∨ (p2 ∧ p4)) → p2) → False) → (False ∨ (False ∧ p1)))) → ((p5 → p3) ∨ p1))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h1.left
    let h10 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3440338895405909467542484393 : (True ∧ (((True ∧ p5) → ((p3 → ((p5 ∧ p5) ∨ p3)) ∧ False)) ∨ ((((False → p4) ∨ p3) → (p2 → ((p1 → p5) ∨ p2))) ∨ p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_752940920152500027169149266191 : (((False ∧ (((p2 ∨ (p5 → ((p4 → p4) → ((True ∨ ((p3 → p3) ∨ (((p4 → p3) → p5) ∨ p5))) → p1)))) ∨ (False ∨ p1)) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110790342508340134022976092619 : (((((((((False ∧ (p1 → ((p3 ∨ True) ∧ p5))) ∧ True) ∨ (p5 → p3)) ∨ False) ∨ (False ∨ (False ∧ p2))) → p2) ∨ p4) ∧ False) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340780670593821658259890071279 : (p2 → (((((((True ∧ (p3 → (True ∨ (p4 ∨ p1)))) ∧ False) ∨ (p1 ∧ (p1 → (False ∧ p3)))) ∧ (p5 ∨ True)) → (True ∨ p2)) → False) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



